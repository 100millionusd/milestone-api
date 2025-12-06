const ethersLib = require('ethers');
// Handle both v5 (exports.ethers) and v6 (exports)
const ethers = ethersLib.ethers || ethersLib;

// Handle v5 vs v6 utils location
const toUtf8Bytes = ethers.toUtf8Bytes || (ethers.utils && ethers.utils.toUtf8Bytes);
const keccak256 = ethers.keccak256 || (ethers.utils && ethers.utils.keccak256);

const stringify = require('json-stable-stringify');


function canonicalize(obj) {
  return stringify(obj, { space: 0 });
}

/**
 * Enrich one bid_audits row: build canonical JSON -> IPFS -> keccak(utf8) -> write ipfs_cid + leaf_hash.
 * Uses audit_id (NOT id).
 * @param {Object} pool - Postgres pool
 * @param {number} auditId - ID of the audit row
 * @param {Function} uploadFn - async (fileObj, tenantId) => { cid, ... }
 */
async function enrichAuditRow(pool, auditId, uploadFn) {
  try {
    // 1) load the audit row
    const { rows } = await pool.query(
      `SELECT audit_id, bid_id, actor_wallet, actor_role, changes, created_at
       FROM bid_audits
       WHERE audit_id = $1`,
      [auditId]
    );
    if (!rows.length) return;
    const row = rows[0];

    // 2) Get tenantId from bids to use tenant-specific Pinata config
    const { rows: bidRows } = await pool.query('SELECT tenant_id FROM bids WHERE bid_id=$1', [row.bid_id]);
    const tenantId = bidRows[0]?.tenant_id;

    // 3) build minimal public-safe JSON
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

    // 4) canonicalize + hash
    const canonical = canonicalize(eventJson);
    const bytes = toUtf8Bytes(canonical);
    const leafHashHex = keccak256(bytes);
    // Store as hex string (Postgres bytea can take hex format \x...) 
    // or if the column is bytea, we can pass a Buffer. 
    // The previous code used Buffer.from(hex, 'hex'). 
    // Let's stick to Buffer for bytea compatibility if needed, or hex string if text.
    // Assuming leaf_hash is BYTEA.
    const leafHash = Buffer.from(leafHashHex.slice(2), 'hex');

    // 5) upload to IPFS using the provided helper (which handles tenant config)
    const fileObj = {
      name: `audit-${auditId}.json`,
      data: Buffer.from(canonical),
      mimetype: 'application/json'
    };

    let cid = null;
    if (typeof uploadFn === 'function') {
      const result = await uploadFn(fileObj, tenantId);
      cid = result.cid;
    } else {
      console.warn('[Audit] No uploadFn provided, skipping IPFS upload');
    }

    // 6) write back
    await pool.query(
      `UPDATE bid_audits
          SET ipfs_cid = $2,
              leaf_hash = $3
        WHERE audit_id = $1`,
      [auditId, cid, leafHash]
    );

    console.log(`[Audit] Enriched audit ${auditId} with CID ${cid}, leafHash=${leafHashHex}`);
  } catch (e) {
    console.error(`[Audit] Failed to enrich audit ${auditId}:`, e);
  }
}

module.exports = { enrichAuditRow };
