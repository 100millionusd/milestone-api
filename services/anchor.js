// services/anchor.js
const { ethers } = require('ethers');
const { keccak256 } = require('ethers/lib/utils');

function parentHash(aBuf, bBuf) {
  const [L, R] = Buffer.compare(aBuf, bBuf) <= 0 ? [aBuf, bBuf] : [bBuf, aBuf];
  return Buffer.from(keccak256(Buffer.concat([L, R])).slice(2), 'hex');
}

function buildTree(leaves) {
  if (!leaves.length) return { root: Buffer.alloc(32, 0), layers: [] };
  let layer = leaves.slice();
  const layers = [layer];
  while (layer.length > 1) {
    const next = [];
    for (let i = 0; i < layer.length; i += 2) {
      const L = layer[i];
      const R = layer[i + 1] || layer[i];
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

/** periodId format: 'YYYY-MM-DDTHH' (24h) */
function periodIdForDate(date = new Date()) {
  // UTC or your preferred timezone; keep consistent everywhere
  const d = new Date(date.toISOString().slice(0, 13)); // hour bucket
  const iso = d.toISOString().slice(0, 13);            // 'YYYY-MM-DDTHH'
  return iso;
}

async function anchorPeriod(pool, periodId) {
  const rows = (await pool.query(
    `SELECT id, leaf_hash
     FROM bid_audits
     WHERE batch_id IS NULL
       AND to_char(created_at AT TIME ZONE 'UTC', 'YYYY-MM-DD"T"HH24') = $1
       AND leaf_hash IS NOT NULL
     ORDER BY id ASC`,
    [periodId]
  )).rows;

  if (!rows.length) return null;

  const leaves = rows.map(r => r.leaf_hash);
  const { root, layers } = buildTree(leaves);

  const provider = new ethers.providers.JsonRpcProvider(process.env.ANCHOR_RPC_URL, Number(process.env.ANCHOR_CHAIN_ID));
  const wallet = new ethers.Wallet(process.env.ANCHOR_PRIVATE_KEY, provider);
  const abi = [
    "function roots(bytes32) view returns (bytes32)",
    "function anchor(bytes32 periodId, bytes32 root) external"
  ];
  const c = new ethers.Contract(process.env.ANCHOR_CONTRACT, abi, wallet);

  const periodBytes32 = ethers.utils.keccak256(Buffer.from(periodId, 'utf8'));
  const rootHex = '0x' + root.toString('hex');

  const tx = await c.anchor(periodBytes32, rootHex);
  const receipt = await tx.wait();

  const batch = (await pool.query(
    `INSERT INTO audit_batches (period_id, merkle_root, chain_id, contract_addr, tx_hash)
     VALUES ($1,$2,$3,$4,$5) RETURNING id`,
    [periodId, root, Number(process.env.ANCHOR_CHAIN_ID), process.env.ANCHOR_CONTRACT, receipt.transactionHash]
  )).rows[0];

  for (let i = 0; i < rows.length; i++) {
    const proof = proofForIndex(layers, i);
    await pool.query(
      `UPDATE bid_audits SET batch_id=$1, merkle_index=$2, merkle_proof=$3 WHERE id=$4`,
      [batch.id, i, proof, rows[i].id]
    );
  }

  return { batchId: batch.id, tx: receipt.transactionHash, root: rootHex, count: rows.length };
}

module.exports = { anchorPeriod, periodIdForDate };
