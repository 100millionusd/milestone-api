// services/auditPinata.js
const stringify = require('json-stable-stringify');
const { keccak256 } = require('ethers/lib/utils');

function canonicalize(obj) {
  return stringify(obj, { space: 0 });
}

async function uploadJsonToPinata(json) {
  const PINATA_JWT = process.env.PINATA_JWT;
  if (!PINATA_JWT) throw new Error('PINATA_JWT not set');
  const doFetch = globalThis.fetch || require('node-fetch');

  const r = await doFetch('https://api.pinata.cloud/pinning/pinJSONToIPFS', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json', Authorization: `Bearer ${PINATA_JWT}` },
    body: JSON.stringify({ pinataContent: json }),
  });
  if (!r.ok) {
    let msg = `Pinata ${r.status}`;
    try { const j = await r.json(); msg = j?.error || msg; } catch {}
    throw new Error(msg);
  }
  const j = await r.json();
  return { cid: j.IpfsHash };
}

/**
 * Take a bid_audits row id, build a canonical JSON, upload to IPFS,
 * compute keccak hash, and write ipfs_cid + leaf_hash back into the row.
 */
async function enrichAuditRow(pool, auditId) {
  // 1) load the audit row
  const { rows } = await pool.query(
    `SELECT id, bid_id, actor_wallet, actor_role, changes, created_at
     FROM bid_audits WHERE id = $1`,
    [auditId]
  );
  if (!rows.length) return;
  const row = rows[0];

  // 2) build a minimal, public-safe event JSON (no PII)
  const changedFields = row.changes && typeof row.changes === 'object'
    ? Object.keys(row.changes)
    : [];
  const eventJson = {
    _schema: 'bid-audit@v1',
    itemType: 'bid',
    itemId: Number(row.bid_id),
    action: 'update',               // your existing route only logs updates; adjust if you add more
    actorRole: row.actor_role || 'admin',
    actorAddress: row.actor_wallet || null,
    changedFields,
    changes: row.changes || null,   // keep the minimal diff object you already write
    createdAt: row.created_at ? new Date(row.created_at).toISOString() : new Date().toISOString(),
  };

  // 3) canonicalize + hash
  const canonical = canonicalize(eventJson);
  const bytes = Buffer.from(canonical, 'utf8');
  const leafHashHex = keccak256(bytes);                // 0x…
  const leafHash = Buffer.from(leafHashHex.slice(2), 'hex');

  // 4) upload to Pinata
  const { cid } = await uploadJsonToPinata(eventJson);

  // 5) write back to the same bid_audits row
  await pool.query(
    `UPDATE bid_audits SET ipfs_cid = $2, leaf_hash = $3 WHERE id = $1`,
    [auditId, cid, leafHash]
  );

  return { cid, leafHash: leafHashHex };
}

module.exports = { enrichAuditRow };
