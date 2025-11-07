// services/anchor.js
// Build & anchor Merkle roots for bid_audits, and link already-anchored periods.
// CommonJS, no TS build required.

const { ethers } = require('ethers');
const { keccak256 } = require('ethers/lib/utils');

/* --------------------------
   Merkle helpers (keccak256)
---------------------------*/
function parentHash(aBuf, bBuf) {
  // Order-agnostic pair hashing (sort bytes)
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
  // Use UTC hour buckets to be deterministic across regions
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
      // decode Error(string)
      const reasonHex = '0x' + data.slice(138);
      const reason = ethers.utils.toUtf8String(reasonHex).toLowerCase();
      if (reason.includes('already anchored')) return true;
    } catch {}
  }
  return false;
}

/* -----------------------------------
   Anchor current period on-chain & DB
------------------------------------*/
async function anchorPeriod(pool, periodId) {
  if (!periodId) periodId = periodIdForDate();

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

  const leaves = rows.map((r) => r.leaf_hash);
  const { root, layers } = buildTree(leaves);

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

  // Inputs
  const periodBytes32 = ethers.utils.keccak256(Buffer.from(periodId, 'utf8'));
  const rootHex = '0x' + root.toString('hex');

  // 2) On-chain check first (IDEMPOTENT)
  const current = await c.roots(periodBytes32);
  if (current && current.toLowerCase() !== ZERO32) {
    if (current.toLowerCase() === rootHex.toLowerCase()) {
      // Already anchored with same root → just link locally
      const linked = await finalizeExistingAnchor(pool, periodId, /* txHash */ null);
      return { ok: true, status: 'already_anchored_linked', ...linked };
    }
    // Different root anchored for this period → do not proceed
    return {
      ok: false,
      status: 'onchain_root_mismatch',
      periodId,
      onchainRoot: current,
      localRoot: rootHex,
      message: 'On-chain root for period differs from local Merkle root.',
    };
  }

  // 3) Preflight + robust gas estimate (handle duplicate safely)
  try {
    // Static call should pass if not anchored; revert reasons bubble here
    await c.callStatic.anchor(periodBytes32, rootHex, { from: wallet.address });
  } catch (e) {
    if (isAlreadyAnchoredError(e)) {
      const linked = await finalizeExistingAnchor(pool, periodId, null);
      return { ok: true, status: 'already_anchored_linked', ...linked };
    }
    throw e;
  }

  let gas;
  try {
    gas = await c.estimateGas.anchor(periodBytes32, rootHex, { from: wallet.address });
  } catch (e) {
    if (isAlreadyAnchoredError(e)) {
      const linked = await finalizeExistingAnchor(pool, periodId, null);
      return { ok: true, status: 'already_anchored_linked', ...linked };
    }
    throw e;
  }

  // pad gas a bit to avoid underestimation on busy L2s
  const pad = Number(process.env.ANCHOR_GAS_PAD || '1.2');
  const gasLimit = ethers.BigNumber.from(gas)
    .mul(Math.floor(pad * 100))
    .div(100);

  const fee = await provider.getFeeData();

  // 4) Send anchor tx
  const tx = await c.anchor(periodBytes32, rootHex, {
    gasLimit,
    maxFeePerGas: fee.maxFeePerGas ?? undefined,
    maxPriorityFeePerGas: fee.maxPriorityFeePerGas ?? undefined,
  });
  const receipt = await tx.wait(1);

  // 5) Persist batch row
  const batch = (
    await pool.query(
      `INSERT INTO audit_batches (period_id, merkle_root, chain_id, contract_addr, tx_hash)
       VALUES ($1,$2,$3,$4,$5)
       ON CONFLICT (period_id) DO UPDATE SET merkle_root=EXCLUDED.merkle_root
       RETURNING id`,
      [
        periodId,
        root, // bytea
        chainId,
        contractAddr,
        receipt.transactionHash,
      ]
    )
  ).rows[0];

  // 6) Attach proofs/index to each audit row
  for (let i = 0; i < rows.length; i++) {
    const proof = proofForIndex(layers, i);
    await pool.query(
      `UPDATE bid_audits
          SET batch_id=$1,
              merkle_index=$2,
              merkle_proof=$3::bytea[]
        WHERE audit_id=$4`,
      [batch.id, i, proof, rows[i].audit_id]
    );
  }

  return {
    ok: true,
    status: 'anchored',
    periodId,
    batchId: batch.id,
    root: rootHex,
    tx: receipt.transactionHash,
    count: rows.length,
  };
}

/* ------------------------------------------------------------
   Finalize an already-anchored period (verify + write to DB)
   Use when you anchored externally and just need to link rows.
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

  // 2) Rebuild Merkle root locally
  const leaves = rows.map((r) => r.leaf_hash);
  const { root, layers } = buildTree(leaves);
  const localRootHex = '0x' + root.toString('hex');

  // 3) Read on-chain root and verify match
  const provider = new ethers.providers.JsonRpcProvider(
    process.env.ANCHOR_RPC_URL,
    Number(process.env.ANCHOR_CHAIN_ID)
  );
  const abi = ['function roots(bytes32) view returns (bytes32)'];
  const c = new ethers.Contract(process.env.ANCHOR_CONTRACT, abi, provider);

  const periodBytes32 = ethers.utils.keccak256(Buffer.from(periodId, 'utf8'));
  const onchainRoot = await c.roots(periodBytes32);

  if (onchainRoot.toLowerCase() !== localRootHex.toLowerCase()) {
    throw new Error(
      `on-chain root mismatch. onchain=${onchainRoot} local=${localRootHex}`
    );
  }

  // 4) Upsert batch row (txHash optional)
  const batch = (
    await pool.query(
      `INSERT INTO audit_batches (period_id, merkle_root, chain_id, contract_addr, tx_hash)
       VALUES ($1,$2,$3,$4,$5)
       ON CONFLICT (period_id) DO UPDATE SET merkle_root=EXCLUDED.merkle_root
       RETURNING id`,
      [
        periodId,
        root, // bytea
        Number(process.env.ANCHOR_CHAIN_ID),
        process.env.ANCHOR_CONTRACT,
        txHash || '0x',
      ]
    )
  ).rows[0];

  // 5) Attach proofs/index to each audit row
  for (let i = 0; i < rows.length; i++) {
    const proof = proofForIndex(layers, i);
    await pool.query(
      `UPDATE bid_audits
          SET batch_id=$1,
              merkle_index=$2,
              merkle_proof=$3::bytea[]
        WHERE audit_id=$4`,
      [batch.id, i, proof, rows[i].audit_id]
    );
  }

  return {
    ok: true,
    periodId,
    batchId: batch.id,
    root: localRootHex,
    count: rows.length,
  };
}

/* -------------
   Exports
-------------*/
module.exports = {
  parentHash,           // exported for tests/debug
  buildTree,
  proofForIndex,
  periodIdForDate,
  anchorPeriod,
  finalizeExistingAnchor,
};
