'use strict';

const express = require('express');

module.exports = function installMultiOrg(app, pool, opts = {}) {
  // ── Behavior flags
  const allowOrg1Fallback = opts.allowOrg1Fallback !== false; // default true
  const ORG1_ID = Number(process.env.ORG1_ID || 1);
  const ENFORCE_ORG_CONFIG = String(process.env.ENFORCE_ORG_CONFIG || 'true').toLowerCase() === 'true';

  // Attach req.org (must run before your other routes)
  app.use(async (req, res, next) => {
    try {
      const raw = (req.headers['x-org-id'] || req.query.orgId || req.headers['x-org'] || '1').toString();
      let orgId = Number(raw);
      if (!Number.isFinite(orgId) || orgId <= 0) orgId = ORG1_ID;
      const { rows } = await pool.query(
        'SELECT org_id, slug, name FROM organizations WHERE org_id=$1 LIMIT 1',
        [orgId]
      );
      req.org = rows[0] || { org_id: ORG1_ID, slug: 'default', name: 'Default Organization' };
      next();
    } catch (e) { next(e); }
  });

  // Helpers
  async function getOrgConfig(orgId) {
    const { rows } = await pool.query('SELECT * FROM org_configs WHERE org_id=$1 LIMIT 1', [orgId]);
    return rows[0] || null;
  }
  async function getOrgSecrets(orgId) {
    const { rows } = await pool.query(
      'SELECT payments_json, messaging_json FROM org_secrets WHERE org_id=$1 LIMIT 1',
      [orgId]
    );
    const s = rows[0] || {};
    return { payments: s.payments_json || null, messaging: s.messaging_json || null };
  }
  function requireOrgConfigured(orgId, kind) {
    if (allowOrg1Fallback && Number(orgId) === ORG1_ID) return; // Org 1 may use env fallback
    if (!ENFORCE_ORG_CONFIG) return;
    const msg = kind === 'payments'
      ? 'ORG_CONFIG_REQUIRED: Payment settings missing for this organization.'
      : 'ORG_CONFIG_REQUIRED: Messaging settings missing for this organization.';
    const err = new Error(msg);
    err.status = 400;
    throw err;
  }

  // Expose helpers for your payment/messaging routes
  app.locals.org = { getOrgConfig, getOrgSecrets, requireOrgConfigured, ORG1_ID, allowOrg1Fallback };

  // Minimal admin endpoints
  const router = express.Router();
  const adminOnly = (req, res, next) => {
    const role = (req.user?.role || '').toLowerCase();
    if (role !== 'admin') return res.status(403).json({ error: 'Admin only' });
    next();
  };

  router.get('/orgs/current', async (req, res) => {
    res.json({ org: req.org });
  });

  router.get('/orgs/current/config', adminOnly, async (req, res) => {
    const [cfg, sec] = await Promise.all([
      getOrgConfig(req.org.org_id),
      getOrgSecrets(req.org.org_id)
    ]);
    res.json({ config: cfg, secrets: { hasPayments: !!sec?.payments, hasMessaging: !!sec?.messaging } });
  });

  router.post('/orgs/current/config', adminOnly, express.json(), async (req, res) => {
    const orgId = req.org.org_id;
    const {
      chain = 'sepolia',
      safe_address = null,
      payment_mode = 'safe',
      currency = 'USD',
      safe_threshold_usd = 0
    } = req.body || {};
    await pool.query(
      `INSERT INTO org_configs (org_id, chain, safe_address, payment_mode, currency, updated_at)
       VALUES ($1,$2,$3,$4,$5, now())
       ON CONFLICT (org_id)
       DO UPDATE SET chain=EXCLUDED.chain, safe_address=EXCLUDED.safe_address,
                     payment_mode=EXCLUDED.payment_mode, currency=EXCLUDED.currency, updated_at=now()`,
      [orgId, chain, safe_address, payment_mode, currency]
    );
    res.json({ ok: true });
  });

  router.post('/orgs/current/secrets', adminOnly, express.json(), async (req, res) => {
    const orgId = req.org.org_id;
    const { payments, messaging } = req.body || {};
    await pool.query(
      `INSERT INTO org_secrets (org_id, payments_json, messaging_json, created_at, updated_at)
       VALUES ($1,$2,$3, now(), now())
       ON CONFLICT (org_id)
       DO UPDATE SET payments_json=COALESCE(EXCLUDED.payments_json, org_secrets.payments_json),
                     messaging_json=COALESCE(EXCLUDED.messaging_json, org_secrets.messaging_json),
                     updated_at=now()`,
      [orgId, payments || null, messaging || null]
    );
    res.json({ ok: true });
  });

  app.use(router);
};
