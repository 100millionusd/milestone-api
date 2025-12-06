// services/anchor.js
// Build & anchor Merkle roots for bid_audits, and link already-anchored periods.
// CommonJS, no TS build required. Idempotent + order auto-detect + per-period advisory lock
// + event-timestamp snapshot so old anchors (earlier in the hour) also match.

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
    } catch { }
  }
  return false;
}

/* --------------------------
   Per-period advisory lock
---------------------------*/
async function withPeriodLock(pool, periodId, fn) {
  // Derive a signed 63-bit key from periodId
  const hex = ethers.utils.keccak256(Buffer.from(periodId, 'utf8')).slice(2);
  const asBig = BigInt('0x' + hex) % (2n ** 63n - 1n);
  const key = asBig.toString();

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

  const dbIndexByAudit = new Map(rows.map((r, i) => [r.audit_id, i]));
  const sortedIndexByAudit = new Map(sortedPairs.map((p, i) => [p.audit_id, i]));

  return {
    db: { rootHex: dbRootHex, tree: dbTree, indexByAudit: dbIndexByAudit, order: 'db' },
    sorted: { rootHex: sortedRootHex, tree: sortedTree, indexByAudit: sortedIndexByAudit, order: 'sorted' },
  };
}

/* --------------------------
   DB row loader (with cutoff)
---------------------------*/
/* --------------------------
   DB row loader (with cutoff)
---------------------------*/
/* --------------------------
   DB row loader (with cutoff)
---------------------------*/
async function loadRowsForPeriod(pool, periodId, cutoffEpochSec /* or null */, tenantId) {
  // Calculate the end of the current period (approx) to ensure we don't grab future data if running ahead
  // But primarily, we want to REMOVE the strict "to_char" equality check for the specific hour
  // so we can grab older orphans.

  if (cutoffEpochSec) {
    // Case A: Linking to an EXISTING anchor (Must be precise to reproduce the tree)
    // We strictly rely on the timestamp cutoff.
    const q = await pool.query(
      `SELECT ba.audit_id, ba.leaf_hash
         FROM bid_audits ba
         JOIN bids b ON b.bid_id = ba.bid_id
        WHERE ba.batch_id IS NULL
          AND ba.leaf_hash IS NOT NULL
          AND b.tenant_id = $3
          -- Fix: Grab this period's data OR any older un-batched data
          AND ba.created_at <= to_timestamp($2)
        ORDER BY ba.audit_id ASC`,
      [periodId, cutoffEpochSec, tenantId]
    );
    return q.rows;
  }

  // Case B: Creating a NEW anchor
  // We grab everything currently available up to the end of this period (or just everything unbatched).
  // To avoid grabbing data from "the future" (if clock skews), we can keep a loose upper bound or just grab all unbatched.

  // Recommended Fix: Grab all unbatched items created up to "Now" (end of this period hour)
  // We assume periodId corresponds to "current processing time". 

  const q = await pool.query(
    `SELECT ba.audit_id, ba.leaf_hash
       FROM bid_audits ba
       JOIN bids b ON b.bid_id = ba.bid_id
      WHERE ba.batch_id IS NULL
        AND ba.leaf_hash IS NOT NULL
        -- Fix: Instead of restricting to ONE hour, we take everything unbatched 
        -- that is created before the next hour starts.
        -- AND ba.created_at < ((to_timestamp($1, 'YYYY-MM-DD"T"HH24') AT TIME ZONE 'UTC') + interval '1 hour')
      ORDER BY ba.audit_id ASC`,
    [periodId, tenantId]
  );
  console.log(`[Anchor] loadRowsForPeriod: period=${periodId}, tenant=${tenantId}, found=${q.rows.length} rows`);
  if (q.rows.length > 0) {
    console.log(`[Anchor] First row created_at: ${q.rows[0].created_at}`);
  } else {
    // Debug: check if any rows exist for this tenant at all
    const check = await pool.query('SELECT count(*) FROM bid_audits ba JOIN bids b ON b.bid_id=ba.bid_id WHERE b.tenant_id=$1 AND ba.batch_id IS NULL', [tenantId]);
    console.log(`[Anchor] Total unbatched rows for tenant: ${check.rows[0].count}`);
  }
  return q.rows;
}

/* --------------------------
   Find anchor timestamp via log
---------------------------*/
// Requires ANCHOR_EVENT_TOPIC0 (keccak of your event signature, e.g. Anchored(bytes32,bytes32))
// and assumes periodId (bytes32) is indexed as topic[1].
async function findAnchorTimestamp(provider, contractAddr, periodBytes32) {
  const topic0 = process.env.ANCHOR_EVENT_TOPIC0; // e.g. 0x<keccak(Anchored(bytes32,bytes32))>
  if (!topic0) return null;

  const latest = await provider.getBlockNumber();
  const fromEnv = process.env.ANCHOR_EVENT_FROM_BLOCK
    ? Number(process.env.ANCHOR_EVENT_FROM_BLOCK) : null;
  const lookback = Number(process.env.ANCHOR_EVENT_LOOKBACK || '500000'); // ~safe default

  const fromBlock = fromEnv != null ? fromEnv : Math.max(0, latest - lookback);

  const logs = await provider.getLogs({
    address: contractAddr,
    fromBlock,
    toBlock: 'latest',
    topics: [topic0, periodBytes32], // topic[1] == periodId bytes32
  });

  if (!logs || logs.length === 0) return null;

  // Take the latest match for this period
  const last = logs[logs.length - 1];
  const blk = await provider.getBlock(last.blockNumber);
  return Number(blk.timestamp); // epoch seconds
}

/* -----------------------------------
   Anchor current period on-chain & DB
------------------------------------*/
async function anchorPeriod(pool, periodId, tenantId, config = {}) {
  if (!periodId) periodId = periodIdForDate();
  if (!tenantId) throw new Error('tenantId required for anchoring');

  return withPeriodLock(pool, periodId + ':' + tenantId, async () => {
    // Env or Config
    const rpcUrl = config.rpcUrl || process.env.ANCHOR_RPC_URL;
    const chainId = Number(config.chainId || process.env.ANCHOR_CHAIN_ID);
    const pk = config.privateKey || process.env.ANCHOR_PRIVATE_KEY;
    const contractAddr = config.contractAddr || process.env.ANCHOR_CONTRACT;

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

    // --- Check chain first ---
    const current = await c.roots(periodBytes32);

    if (current && current.toLowerCase() !== ZERO32) {
      // It is already anchored on-chain. Try to match the exact snapshot using the event timestamp.
      const anchorTs = await findAnchorTimestamp(provider, contractAddr, periodBytes32).catch(() => null);
      const rows = await loadRowsForPeriod(pool, periodId, anchorTs, tenantId);
      if (!rows.length) {
        return { ok: true, message: 'nothing to link for this period', periodId, count: 0 };
      }
      const variants = buildBothVariants(rows);

      if (current.toLowerCase() === variants.db.rootHex.toLowerCase()) {
        return await _linkWithVariant(pool, periodId, chainId, contractAddr, /*tx*/ null, rows, variants.db);
      }
      if (current.toLowerCase() === variants.sorted.rootHex.toLowerCase()) {
        return await _linkWithVariant(pool, periodId, chainId, contractAddr, /*tx*/ null, rows, variants.sorted);
      }

      return {
        ok: false,
        status: 'onchain_root_mismatch',
        periodId,
        onchainRoot: current,
        localRootDb: variants.db.rootHex,
        localRootSorted: variants.sorted.rootHex,
        snapshot: anchorTs ? `cutoff<=${anchorTs}` : 'no_anchor_timestamp',
        message: 'On-chain root differs from both DB-order and sorted roots (even at event snapshot).',
      };
    }

    // --- Not anchored yet: compute leaves now (full hour to-date) ---
    const rows = await loadRowsForPeriod(pool, periodId, /*cutoff*/ null, tenantId);
    if (!rows.length) {
      return { ok: true, message: 'nothing to anchor for this period', periodId, count: 0 };
    }

    const variants = buildBothVariants(rows);
    const CANON = (process.env.MERKLE_CANON_ORDER || 'sorted').toLowerCase() === 'db'
      ? variants.db : variants.sorted;

    // Preflight (race-safe)
    const rootHex = CANON.rootHex;
    try {
      await c.callStatic.anchor(periodBytes32, rootHex, { from: wallet.address });
    } catch (e) {
      if (isAlreadyAnchoredError(e)) {
        // Someone anchored in the meantime — re-check & link with snapshot
        const cur2 = await c.roots(periodBytes32);
        if (cur2 && cur2.toLowerCase() !== ZERO32) {
          const anchorTs = await findAnchorTimestamp(provider, contractAddr, periodBytes32).catch(() => null);
          const rows2 = await loadRowsForPeriod(pool, periodId, anchorTs, tenantId);
          const v2 = buildBothVariants(rows2);
          if (cur2.toLowerCase() === v2.db.rootHex.toLowerCase()) {
            return await _linkWithVariant(pool, periodId, chainId, contractAddr, null, rows2, v2.db);
          }
          if (cur2.toLowerCase() === v2.sorted.rootHex.toLowerCase()) {
            return await _linkWithVariant(pool, periodId, chainId, contractAddr, null, rows2, v2.sorted);
          }
          return {
            ok: false,
            status: 'onchain_root_mismatch_after_race',
            periodId,
            onchainRoot: cur2,
            localRootDb: v2.db.rootHex,
            localRootSorted: v2.sorted.rootHex,
          };
        }
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
        if (cur2 && cur2.toLowerCase() !== ZERO32) {
          const anchorTs = await findAnchorTimestamp(provider, contractAddr, periodBytes32).catch(() => null);
          const rows2 = await loadRowsForPeriod(pool, periodId, anchorTs, tenantId);
          const v2 = buildBothVariants(rows2);
          if (cur2.toLowerCase() === v2.db.rootHex.toLowerCase()) {
            return await _linkWithVariant(pool, periodId, chainId, contractAddr, null, rows2, v2.db);
          }
          if (cur2.toLowerCase() === v2.sorted.rootHex.toLowerCase()) {
            return await _linkWithVariant(pool, periodId, chainId, contractAddr, null, rows2, v2.sorted);
          }
          return {
            ok: false,
            status: 'onchain_root_mismatch_after_estimate',
            periodId,
            onchainRoot: cur2,
            localRootDb: v2.db.rootHex,
            localRootSorted: v2.sorted.rootHex,
          };
        }
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
   Auto-detects leaf order & uses event timestamp snapshot if available.
-------------------------------------------------------------*/
async function finalizeExistingAnchor(pool, periodId, txHash = null, tenantId, config = {}) {
  if (!periodId) throw new Error('periodId (YYYY-MM-DDTHH) required');
  if (!tenantId) throw new Error('tenantId required');

  const rpcUrl = config.rpcUrl || process.env.ANCHOR_RPC_URL;
  const chainId = Number(config.chainId || process.env.ANCHOR_CHAIN_ID);
  const contractAddr = config.contractAddr || process.env.ANCHOR_CONTRACT;
  if (!rpcUrl || !chainId || !contractAddr) throw new Error('ANCHOR envs missing');

  const provider = new ethers.providers.JsonRpcProvider(rpcUrl, chainId);
  const abi = ['function roots(bytes32) view returns (bytes32)'];
  const c = new ethers.Contract(contractAddr, abi, provider);

  const periodBytes32 = ethers.utils.keccak256(Buffer.from(periodId, 'utf8'));
  const onchainRoot = await c.roots(periodBytes32);
  if (!onchainRoot || onchainRoot.toLowerCase() === ZERO32) {
    throw new Error('on-chain period is not anchored');
  }

  // Try to find the anchor block timestamp for precise snapshot
  const anchorTs = await findAnchorTimestamp(provider, contractAddr, periodBytes32).catch(() => null);
  const rows = await loadRowsForPeriod(pool, periodId, anchorTs, tenantId);

  if (!rows.length) return { ok: true, message: 'nothing to link', periodId, count: 0 };

  const variants = buildBothVariants(rows);
  if (onchainRoot.toLowerCase() === variants.db.rootHex.toLowerCase()) {
    return await _linkWithVariant(pool, periodId, chainId, contractAddr, txHash, rows, variants.db);
  }
  if (onchainRoot.toLowerCase() === variants.sorted.rootHex.toLowerCase()) {
    return await _linkWithVariant(pool, periodId, chainId, contractAddr, txHash, rows, variants.sorted);
  }

  return {
    ok: false,
    status: 'onchain_root_mismatch',
    periodId,
    onchainRoot,
    localRootDb: variants.db.rootHex,
    localRootSorted: variants.sorted.rootHex,
    snapshot: anchorTs ? `cutoff<=${anchorTs}` : 'no_anchor_timestamp',
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
