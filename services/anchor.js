// services/anchor.js
// Build & anchor Merkle roots for bid_audits, and link already-anchored periods.
// CommonJS, no TS build required. Idempotent + order auto-detect on finalize + per-period advisory lock.

const { ethers } = require('ethers');
const { keccak256 } = require('ethers/lib/utils');

/* --------------------------
   Merkle helpers (keccak256)
---------------------------*/
function parentHash(aBuf, bBuf) {
  // Order-agnostic pair hashing (sort bytes PER PAIR)
  const [L, R] = Buffer.compare(aBuf, bBuf) <= 0 ? [aBuf, bBuf] : [bBuf, aBuf];
  return Buffer.from(keccak256(Buffer.concat([L, R])).slice(2), 'hex');
}

function buildTree(leaves) {
  if (!leaves || leaves.length === 0) {
    return { root: Buffer.alloc(32, 0), layers: [] };
  }
  let layer = leaves.slice();
  const layers = [layer];
  while (layer.length > 1) {
    const next = [];
    for (let i = 0; i < layer.length; i += 2) {
      const L = layer[i];
      const R = layer[i + 1] || layer[i]; // duplicate last if odd
      next.push(parentHash(L, R));
    }
    layer = next;
    layers.push(layer);
  }
  return { root: layer[0], layers };
}

function proofForIndex(layers, index) {
  const proof = [];
  let idx = index;
  for (let d = 0; d < layers.length - 1; d++) {
    const layer = layers[d];
    const sib = layer[idx ^ 1] || layer[idx];
    proof.push(sib);
    idx = Math.floor(idx / 2);
  }
  return proof;
}

/* --------------------------
   Period bucketing (UTC)
   Format: 'YYYY-MM-DDTHH'
---------------------------*/
function periodIdForDate(date = new Date()) {
  const y = date.getUTCFullYear();
  const m = String(date.getUTCMonth() + 1).padStart(2, '0');
  const d = String(date.getUTCDate()).padStart(2, '0');
  const h = String(date.getUTCHours()).padStart(2, '0');
  return `${y}-${m}-${d}T${h}`;
}

/* --------------------------
   Idempotency helpers
---------------------------*/
const ZERO32 = '0x0000000000000000000000000000000000000000000000000000000000000000';

function isAlreadyAnchoredError(err) {
  const msg =
    `${err?.reason || err?.error?.message || err?.message || ''}`.toLowerCase();
  if (msg.includes('already anchored')) return true;

  const data = err?.error?.data || err?.data;
  if (typeof data === 'string' && data.startsWith('0x08c379a0')) {
    try {
      const reasonHex = '0x' + data.slice(138);
      const reason = ethers.utils.toUtf8String(reasonHex).toLowerCase();
      if (reason.includes('already anchored')) return true;
    } catch {}
  }
  return false;
}

/* --------------------------
   Per-period advisory lock
---------------------------*/
async function withPeriodLock(pool, periodId, fn) {
  // Derive a signed 63-bit key from periodId
  const hex = ethers.utils.keccak256(Buffer.from(periodId, 'utf8')).slice(2);
  const asBig = BigInt('0x' + hex) % (2n ** 63n - 1n); // fit signed bigint
  const key = asBig.toString(); // pass as string -> numeric in pg

  const got = await pool.query('SELECT pg_try_advisory_lock($1)::boolean AS ok', [key]);
  if (!got.rows?.[0]?.ok) throw new Error('anchor_locked');

  try {
    return await fn();
  } finally {
    await pool.query('SELECT pg_advisory_unlock($1)', [key]);
  }
}

/* --------------------------
   Canonical leaf ordering
---------------------------*/
// Returns both "db-order" and "sorted lexicographic" variants so we can
// compare roots and pick the one that matches on-chain.
function buildBothVariants(rows) {
  // rows: [{ audit_id, leaf_hash: Buffer }]
  const dbLeaves = rows.map(r => r.leaf_hash);
  const dbTree = buildTree(dbLeaves);
  const dbRootHex = '0x' + dbTree.root.toString('hex');

  // sorted by raw bytes ascending
  const sortedPairs = rows
    .map((r, i) => ({ audit_id: r.audit_id, leaf: r.leaf_hash, origIndex: i }))
    .sort((a, b) => Buffer.compare(a.leaf, b.leaf));
  const sortedLeaves = sortedPairs.map(p => p.leaf);
  const sortedTree = buildTree(sortedLeaves);
  const sortedRootHex = '0x' + sortedTree.root.toString('hex');

  // map: audit_id -> index in chosen order
  const dbIndexByAudit = new Map(rows.map((r, i) => [r.audit_id, i]));
  const sortedIndexByAudit = new Map(sortedPairs.map((p, i) => [p.audit_id, i]));

  return {
    db: {
      rootHex: dbRootHex,
      tree: dbTree,
      indexByAudit: dbIndexByAudit,
      order: 'db',
    },
    sorted: {
      rootHex: sortedRootHex,
      tree: sortedTree,
      indexByAudit: sortedIndexByAudit,
      order: 'sorted',
    },
  };
}

/* -----------------------------------
   Anchor current period on-chain & DB
------------------------------------*/
async function anchorPeriod(pool, periodId) {
  if (!periodId) periodId = periodIdForDate();

  return withPeriodLock(pool, periodId, async () => {
    // 1) Collect unbatched leaves for this period (UTC hour)
    const rows = (
      await pool.query(
        `SELECT audit_id, leaf_hash
           FROM bid_audits
          WHERE batch_id IS NULL
            AND leaf_hash IS NOT NULL
            AND to_char(created_at AT TIME ZONE 'UTC','YYYY-MM-DD"T"HH24') = $1
          ORDER BY audit_id ASC`,
        [periodId]
      )
    ).rows;

    if (!rows.length) {
      return { ok: true, message: 'nothing to anchor for this period', periodId, count: 0 };
    }

    // Env
    const rpcUrl = process.env.ANCHOR_RPC_URL;
    const chainId = Number(process.env.ANCHOR_CHAIN_ID);
    const pk = process.env.ANCHOR_PRIVATE_KEY;
    const contractAddr = process.env.ANCHOR_CONTRACT;

    if (!rpcUrl) throw new Error('ANCHOR_RPC_URL not set');
    if (!chainId) throw new Error('ANCHOR_CHAIN_ID not set');
    if (!pk) throw new Error('ANCHOR_PRIVATE_KEY not set');
    if (!contractAddr) throw new Error('ANCHOR_CONTRACT not set');

    const provider = new ethers.providers.JsonRpcProvider(rpcUrl, chainId);
    const wallet = new ethers.Wallet(pk, provider);
    const abi = [
      'function roots(bytes32) view returns (bytes32)',
      'function anchor(bytes32 periodId, bytes32 root) external',
    ];
    const c = new ethers.Contract(contractAddr, abi, wallet);

    const periodBytes32 = ethers.utils.keccak256(Buffer.from(periodId, 'utf8'));

    // 2) Compute both DB-order and Sorted-order roots (for compatibility)
    const variants = buildBothVariants(rows);

    // 3) On-chain check first (IDEMPOTENT)
    const current = await c.roots(periodBytes32);
    if (current && current.toLowerCase() !== ZERO32) {
      // Already anchored on-chain → choose the local variant that matches and link
      if (current.toLowerCase() === variants.db.rootHex.toLowerCase()) {
        return await _linkWithVariant(pool, periodId, chainId, contractAddr, /*tx*/ null, rows, variants.db);
      }
      if (current.toLowerCase() === variants.sorted.rootHex.toLowerCase()) {
        return await _linkWithVariant(pool, periodId, chainId, contractAddr, /*tx*/ null, rows, variants.sorted);
      }
      // Neither variant matches → different snapshot/order/timestamp
      return {
        ok: false,
        status: 'onchain_root_mismatch',
        periodId,
        onchainRoot: current,
        localRootDb: variants.db.rootHex,
        localRootSorted: variants.sorted.rootHex,
        message: 'On-chain root differs from both DB-order and lexicographic-sorted roots.',
      };
    }

    // 4) Not anchored yet: choose canonical order (default: SORTED for cross-system determinism)
    const CANON = (process.env.MERKLE_CANON_ORDER || 'sorted').toLowerCase() === 'db'
      ? variants.db : variants.sorted;

    // Preflight static call (idempotent race-safe)
    const rootHex = CANON.rootHex;
    try {
      await c.callStatic.anchor(periodBytes32, rootHex, { from: wallet.address });
    } catch (e) {
      if (isAlreadyAnchoredError(e)) {
        // Someone anchored in the meantime — re-check and link via finalize path:
        const cur2 = await c.roots(periodBytes32);
        if (cur2 && cur2.toLowerCase() === variants.db.rootHex.toLowerCase()) {
          return await _linkWithVariant(pool, periodId, chainId, contractAddr, null, rows, variants.db);
        }
        if (cur2 && cur2.toLowerCase() === variants.sorted.rootHex.toLowerCase()) {
          return await _linkWithVariant(pool, periodId, chainId, contractAddr, null, rows, variants.sorted);
        }
        return {
          ok: false,
          status: 'onchain_root_mismatch_after_race',
          periodId,
          onchainRoot: cur2,
          localRootDb: variants.db.rootHex,
          localRootSorted: variants.sorted.rootHex,
        };
      }
      throw e;
    }

    // Estimate & send
    let gas;
    try {
      gas = await c.estimateGas.anchor(periodBytes32, rootHex, { from: wallet.address });
    } catch (e) {
      if (isAlreadyAnchoredError(e)) {
        const cur2 = await c.roots(periodBytes32);
        if (cur2 && cur2.toLowerCase() === variants.db.rootHex.toLowerCase()) {
          return await _linkWithVariant(pool, periodId, chainId, contractAddr, null, rows, variants.db);
        }
        if (cur2 && cur2.toLowerCase() === variants.sorted.rootHex.toLowerCase()) {
          return await _linkWithVariant(pool, periodId, chainId, contractAddr, null, rows, variants.sorted);
        }
        return {
          ok: false,
          status: 'onchain_root_mismatch_after_estimate',
          periodId,
          onchainRoot: cur2,
          localRootDb: variants.db.rootHex,
          localRootSorted: variants.sorted.rootHex,
        };
      }
      throw e;
    }

    const pad = Number(process.env.ANCHOR_GAS_PAD || '1.2');
    const gasLimit = ethers.BigNumber.from(gas).mul(Math.floor(pad * 100)).div(100);
    const fee = await provider.getFeeData();

    const tx = await c.anchor(periodBytes32, rootHex, {
      gasLimit,
      maxFeePerGas: fee.maxFeePerGas ?? undefined,
      maxPriorityFeePerGas: fee.maxPriorityFeePerGas ?? undefined,
    });
    const receipt = await tx.wait(1);

    return await _linkWithVariant(pool, periodId, chainId, contractAddr, receipt.transactionHash, rows, CANON);
  });
}

/* ------------------------------------------------------------
   Finalize an already-anchored period (verify + write to DB)
   Auto-detects leaf order that matches on-chain root (db vs sorted).
-------------------------------------------------------------*/
async function finalizeExistingAnchor(pool, periodId, txHash = null) {
  if (!periodId) throw new Error('periodId (YYYY-MM-DDTHH) required');

  // 1) Load rows for this period (UTC hour), unbatched
  const rows = (
    await pool.query(
      `SELECT audit_id, leaf_hash
         FROM bid_audits
        WHERE to_char(created_at AT TIME ZONE 'UTC','YYYY-MM-DD"T"HH24') = $1
          AND leaf_hash IS NOT NULL
          AND batch_id IS NULL
        ORDER BY audit_id ASC`,
      [periodId]
    )
  ).rows;

  if (!rows.length) return { ok: true, message: 'nothing to link', periodId, count: 0 };

  // 2) On-chain root
  const provider = new ethers.providers.JsonRpcProvider(
    process.env.ANCHOR_RPC_URL,
    Number(process.env.ANCHOR_CHAIN_ID)
  );
  const abi = ['function roots(bytes32) view returns (bytes32)'];
  const c = new ethers.Contract(process.env.ANCHOR_CONTRACT, abi, provider);

  const periodBytes32 = ethers.utils.keccak256(Buffer.from(periodId, 'utf8'));
  const onchainRoot = await c.roots(periodBytes32);
  if (!onchainRoot || onchainRoot.toLowerCase() === ZERO32) {
    throw new Error('on-chain period is not anchored');
  }

  // 3) Build both variants and pick the one that matches
  const variants = buildBothVariants(rows);
  if (onchainRoot.toLowerCase() === variants.db.rootHex.toLowerCase()) {
    return await _linkWithVariant(pool, periodId, Number(process.env.ANCHOR_CHAIN_ID), process.env.ANCHOR_CONTRACT, txHash, rows, variants.db);
  }
  if (onchainRoot.toLowerCase() === variants.sorted.rootHex.toLowerCase()) {
    return await _linkWithVariant(pool, periodId, Number(process.env.ANCHOR_CHAIN_ID), process.env.ANCHOR_CONTRACT, txHash, rows, variants.sorted);
  }

  // Neither matches -> different snapshot/timestamp/order
  return {
    ok: false,
    status: 'onchain_root_mismatch',
    periodId,
    onchainRoot,
    localRootDb: variants.db.rootHex,
    localRootSorted: variants.sorted.rootHex,
    message: 'On-chain root differs from both DB-order and lexicographic-sorted roots.',
  };
}

/* -----------------------------------
   Internal: link using chosen variant
------------------------------------*/
async function _linkWithVariant(pool, periodId, chainId, contractAddr, txHash, rows, variant) {
  const { tree, indexByAudit, order } = variant;

  // Upsert batch row
  const batch = (
    await pool.query(
      `INSERT INTO audit_batches (period_id, merkle_root, chain_id, contract_addr, tx_hash)
       VALUES ($1,$2,$3,$4,$5)
       ON CONFLICT (period_id) DO UPDATE SET merkle_root=EXCLUDED.merkle_root
       RETURNING id`,
      [
        periodId,
        tree.root, // bytea
        chainId,
        contractAddr,
        txHash || '0x',
      ]
    )
  ).rows[0];

  // Attach proofs/index using the chosen order
  for (const r of rows) {
    const idx = indexByAudit.get(r.audit_id);
    const proof = proofForIndex(tree.layers, idx);
    await pool.query(
      `UPDATE bid_audits
          SET batch_id=$1,
              merkle_index=$2,
              merkle_proof=$3::bytea[],
              merkle_order=$4
        WHERE audit_id=$5`,
      [batch.id, idx, proof, order, r.audit_id]
    );
  }

  return {
    ok: true,
    status: txHash ? 'anchored' : `linked_${order}_order`,
    periodId,
    batchId: batch.id,
    root: '0x' + tree.root.toString('hex'),
    tx: txHash || null,
    count: rows.length,
    order,
  };
}

/* -------------
   Exports
-------------*/
module.exports = {
  parentHash,
  buildTree,
  proofForIndex,
  periodIdForDate,
  anchorPeriod,
  finalizeExistingAnchor,
};
