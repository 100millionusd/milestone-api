require('dotenv').config();
const { Pool } = require('pg');

const pool = new Pool({
    connectionString: process.env.DATABASE_URL,
});

async function run() {
    console.log("Checking bid_audits...");
    try {
        const res = await pool.query(`
      SELECT ba.audit_id, ba.bid_id, ba.leaf_hash, ba.batch_id, ba.created_at, b.tenant_id
      FROM bid_audits ba
      JOIN bids b ON b.bid_id = ba.bid_id
      ORDER BY ba.created_at DESC
      LIMIT 10
    `);
        console.table(res.rows.map(r => ({
            ...r,
            leaf_hash: r.leaf_hash ? r.leaf_hash.toString('hex').slice(0, 10) + '...' : 'NULL',
            created_at: r.created_at.toISOString()
        })));
    } catch (e) {
        console.error("Query failed:", e);
    }
    pool.end();
}

run();
