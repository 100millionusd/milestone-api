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
 * Enrich one bid_audits row: build canonical JSON -> IPFS -> keccak(utf8) -> write ipfs_cid + leaf_hash.
 * Uses audit_id (NOT id).
 */
async function enrichAuditRow(pool, auditId) {
  // 1) load the audit row
  const { rows } = await pool.query(
    `SELECT audit_id, bid_id, actor_wallet, actor_role, changes, created_at
       FROM bid_audits
      WHERE audit_id = $1`,
    [auditId]
  );
  if (!rows.length) return;
  const row = rows[0];

  // 2) build minimal public-safe JSON
  const changedFields = row.changes && typeof row.changes === 'object'
    ? Object.keys(row.changes)
    : [];
  const eventJson = {
    _schema: 'bid-audit@v1',
    itemType: 'bid',
    itemId: Number(row.bid_id),
    action: 'update',
    actorRole: row.actor_role || 'admin',
    actorAddress: row.actor_wallet || null,
    changedFields,
    changes: row.changes || null,
    createdAt: row.created_at ? new Date(row.created_at).toISOString() : new Date().toISOString(),
  };

  // 3) canonicalize + hash
  const canonical = canonicalize(eventJson);
  const bytes = Buffer.from(canonical, 'utf8');
  const leafHashHex = keccak256(bytes);
  const leafHash = Buffer.from(leafHashHex.slice(2), 'hex');

  // 4) upload to IPFS
  const { cid } = await uploadJsonToPinata(eventJson);

  // 5) write back
  await pool.query(
    `UPDATE bid_audits
        SET ipfs_cid = $2,
            leaf_hash = $3
      WHERE audit_id = $1`,
    [auditId, cid, leafHash]
  );

  return { cid, leafHash: leafHashHex };
}

module.exports = { enrichAuditRow };
