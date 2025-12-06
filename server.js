// server.js — Milestone API (Postgres + Blockchain + IPFS + Agent2 + robust PDF parsing)
// ======================================================================================
// This server exposes a minimal-but-complete API for LithiumX with:
//   • Postgres persistence
//   • Express endpoints for proposals, bids, proofs, payments, vendor helpers
//   • Blockchain token transfers (USDC/USDT on Sepolia)
//   • IPFS uploads via Pinata (file + JSON)
//   • Agent2 bid analysis powered by OpenAI with PDF extraction + retries
//   • Strong GET no-cache headers so polling always sees fresh data
//   • Inline Agent2 analysis on bid creation (response already includes ai_analysis)
//   • Manual analyze endpoint for retries (admin or bid owner)
//   • Agent2 analysis of PROOFS (text + file links) stored on proofs.ai_analysis
//
// Environment variables (commonly used):
//   PORT                      - default 3000
//   DATABASE_URL              - Postgres connection string
//   CORS_ORIGINS              - comma-separated allowed origins (default: https://lithiumx.netlify.app)
//   OPENAI_API_KEY            - required for Agent2
//   OPENAI_PROJECT            - optional OpenAI project id
//   OPENAI_ORG                - optional OpenAI org id
//   SEPOLIA_RPC_URL           - Ethereum Sepolia RPC (default publicnode)
//   PRIVATE_KEY               - Hex private key for token transfers (no 0x is okay)
//   USDC_ADDRESS / USDT_ADDRESS
//   PINATA_API_KEY / PINATA_SECRET_API_KEY
//   PINATA_GATEWAY_DOMAIN     - gateway domain (default: gateway.pinata.cloud)
//   ADMIN_ADDRESSES           - comma-separated admin wallet addresses
//   JWT_SECRET                - secret for signing auth JWTs
//   ENFORCE_JWT_ADMIN         - "true" to require admin JWT on admin routes (default false for compatibility)
//   SCOPE_BIDS_FOR_VENDOR     - "true" to scope GET /bids to caller's address if vendor (default false)
// --------------------------------------------------------------------------------------


require("dotenv").config();
const express = require("express");
const cors = require("cors");
const helmet = require("helmet");
const fileUpload = require("express-fileupload");
const FormData = require("form-data");
const https = require("https");
const http = require("http");
const { ethers } = require("ethers");
const Joi = require("joi");
const { Pool } = require("pg");
const { anchorPeriod, periodIdForDate, finalizeExistingAnchor } = require('./services/anchor');
const { exiftool } = require("exiftool-vendored");
const os = require("os");
const fs = require("fs/promises");
const path = require("path");
const crypto = require("crypto");
const pdfParse = require("pdf-parse");
const OpenAI = require("openai");
const { enrichAuditRow } = require('./services/auditPinata');

// --- robust tx-hash extractor (handles strings, fields, functions, nested, promises) ---
async function extractTxHash(sendRes) {
  if (!sendRes) return null;

  const take = (v) =>
    (typeof v === 'string' && v.startsWith('0x') && v.length >= 66) ? v : null;

  // direct string
  let v = take(sendRes);
  if (v) return v;

  // common direct fields
  for (const k of ['hash', 'transactionHash', 'txHash', 'txid', 'id', 'tx']) {
    v = take(sendRes[k]);
    if (v) return v;
  }

  // functional getters
  if (typeof sendRes.hash === 'function') {
    try { v = take(await sendRes.hash()); if (v) return v; } catch { }
  }
  if (typeof sendRes.getHash === 'function') {
    try { v = take(await sendRes.getHash()); if (v) return v; } catch { }
  }

  // nested common containers
  for (const n of ['receipt', 'data', 'result']) {
    const obj = sendRes[n];
    if (!obj) continue;
    for (const k of ['transactionHash', 'hash', 'txHash', 'txid', 'id', 'tx']) {
      v = take(obj[k]);
      if (v) return v;
    }
  }

  // ethers-style wait()
  if (typeof sendRes.wait === 'function') {
    try {
      const rcpt = await sendRes.wait(1);
      v = take(rcpt?.transactionHash) || take(rcpt?.hash);
      if (v) return v;
    } catch { }
  }

  return null;
}

// ==== SAFE CONFIG (define once, near the top) ====
const ENCRYPTION_KEY = process.env.ENCRYPTION_KEY || crypto.createHash('sha256').update(String(process.env.JWT_SECRET || 'dev_secret')).digest().slice(0, 32);
const IV_LENGTH = 16;

const SAFE_ADDRESS = (process.env.SAFE_ADDRESS || process.env.SAFE_WALLET || '0xedd1F37FD3eaACb596CDF00102187DA0cc884D93').trim();
const SAFE_TXSERVICE_URL = (process.env.SAFE_TXSERVICE_URL || 'https://api.safe.global/tx-service/sep').trim().replace(/\/+$/, '');
const SAFE_THRESHOLD_USD = Number(process.env.SAFE_THRESHOLD_USD || 0);

// --- Safe TxService rate-limit aware fetch (+auth) ---
const SAFE_MAX_RETRIES = Number(process.env.SAFE_MAX_RETRIES || 4);
const SAFE_BASE_BACKOFF_MS = Number(process.env.SAFE_BASE_BACKOFF_MS || 400);

const _safeWait = (ms) => new Promise((r) => setTimeout(r, ms));
const _parseRetryAfter = (val) => {
  if (!val) return null;
  const s = Number(val);
  if (Number.isFinite(s)) return s * 1000;
  const d = Date.parse(val);
  if (Number.isFinite(d)) return Math.max(0, d - Date.now());
  return null;
};

async function safeFetchRL(url, opts = {}, attempt = 0) {
  const headers = {
    Accept: "application/json",
    ...(opts.headers || {}),
  };
  // add API key if present
  if (process.env.SAFE_API_KEY) headers.Authorization = `Bearer ${process.env.SAFE_API_KEY}`;

  const res = await fetch(url, { ...opts, headers });

  if ((res.status === 429 || res.status === 503) && attempt < SAFE_MAX_RETRIES) {
    const ra = res.headers.get("retry-after");
    const delay =
      _parseRetryAfter(ra) ??
      Math.min(SAFE_BASE_BACKOFF_MS * (2 ** attempt) + Math.floor(Math.random() * 150), 5000);
    await _safeWait(delay);
    return safeFetchRL(url, opts, attempt + 1);
  }
  return res;
}

// 🔐 auth utilities
const cookieParser = require("cookie-parser");
const jwt = require("jsonwebtoken");

let __vendorSeedGuard = 0;

// ==== JWT helpers (put near top of server.js) ====

function readJwtFromReq(req) {
  // 1) Authorization: Bearer <token>
  const h = String(req.headers?.authorization || '');
  if (h.startsWith('Bearer ')) return h.slice(7).trim();

  // 2) Cookies: auth_token (backend) or lx_jwt (frontend sync)
  const c = req.cookies || {};
  if (c.auth_token && String(c.auth_token).trim()) return String(c.auth_token).trim();
  if (c.lx_jwt && String(c.lx_jwt).trim()) return String(c.lx_jwt).trim();

  return null;
}

function verifyJwt(t) {
  try {
    const p = jwt.verify(t, JWT_SECRET);
    return p && typeof p === 'object' ? p : null;
  } catch {
    return null;
  }
}

// === ROLE HELPERS (paste once, under auth utilities; do NOT redeclare JWT_SECRET) =========
const VALID_ROLES = ['vendor', 'proposer', 'admin', 'reporter']; // ✅ Added 'reporter'

/** normalize role intent from query/body */
function normalizeRoleIntent(v) {
  return String(v || '').trim().toLowerCase();
}

/** decide effective role given durable roles + optional explicit intent */
function roleFromDurableOrIntent(roles, intent) {
  if (!Array.isArray(roles)) roles = [];
  // if they already only have one durable role and no intent, use it
  if (roles.length === 1 && !intent) return roles[0];
  // explicit intent wins (only allow vendor/proposer/reporter here)
  if (intent === 'vendor' || intent === 'proposer' || intent === 'reporter') return intent;
  // 🛑 FIX: Allow admin intent ONLY if they actually have the admin role
  if (intent === 'admin' && roles.includes('admin')) return 'admin';
  // if there’s a single non-admin durable role, pick it
  const nonAdmin = roles.filter(r => r !== 'admin');
  if (nonAdmin.length === 1) return nonAdmin[0];
  // otherwise force the client to choose
  return null;
}

/** durable roles = what the wallet actually has in DB (plus admin) */
async function durableRolesForAddress(address, tenantId) {
  const addr = String(address || '').toLowerCase();
  const roles = [];

  try {
    if (isAdminAddress(addr)) roles.push('admin');
  } catch { }

  try {
    const v = await pool.query(
      `SELECT 1 FROM vendor_profiles WHERE lower(wallet_address)=lower($1) AND tenant_id=$2 LIMIT 1`,
      [addr, tenantId]
    );
    if (v.rowCount > 0) roles.push('vendor');
  } catch { }

  try {
    const p = await pool.query(
      `SELECT 1 FROM proposals WHERE lower(owner_wallet)=lower($1) AND tenant_id=$2 LIMIT 1`,
      [addr, tenantId]
    );
    if (p.rowCount > 0) roles.push('proposer');
  } catch { }

  try {
    const r = await pool.query(
      `SELECT 1 FROM proposer_profiles WHERE lower(wallet_address)=lower($1) AND tenant_id=$2 LIMIT 1`,
      [addr, tenantId]
    );
    if (r.rowCount > 0) roles.push('proposer');
  } catch { }

  // ✅ NEW: Check tenant_members (for tenant admins)
  try {
    const m = await pool.query(
      `SELECT role FROM tenant_members WHERE lower(wallet_address)=lower($1) AND tenant_id=$2`,
      [addr, tenantId]
    );
    console.log('[Auth] durableRolesForAddress: Checking tenant_members for', addr, 'tenant:', tenantId, 'Found:', m.rows);
    for (const row of m.rows) {
      if (row.role) roles.push(row.role);
    }
  } catch (e) {
    console.error('[Auth] durableRolesForAddress error checking tenant_members:', e);
  }

  return roles;
}

// Put near your other helpers
function _addrText(a, city, country) {
  if (!a) return null;
  if (typeof a === 'string') return a;
  const line = a.line1 || a.address1 || '';
  const cty = a.city ?? city ?? '';
  const ctry = a.country ?? country ?? '';
  const out = [line, cty, ctry].filter(Boolean).join(', ');
  return out || null;
}

// Canonical vendor seeder: copy fields from user_profiles → vendor_profiles
async function seedVendorFromUserProfile(pool, wallet, tenantId) {
  const w = String(wallet || '').toLowerCase();
  if (!w) return false;

  __vendorSeedGuard++; // temporarily allow vendor insert past the global guard
  try {
    const { rowCount } = await pool.query(
      `INSERT INTO vendor_profiles
         (wallet_address, vendor_name, email, phone, website, address, status, created_at, updated_at, telegram_chat_id, whatsapp, tenant_id)
       SELECT $1,
              COALESCE(display_name,''),
              email, phone, website, address,
              'pending', NOW(), NOW(),
              telegram_chat_id, whatsapp,
              $2
         FROM user_profiles
        WHERE lower(wallet_address)=lower($1)
       ON CONFLICT (wallet_address) DO UPDATE SET
         vendor_name       = COALESCE(NULLIF(EXCLUDED.vendor_name,''), vendor_profiles.vendor_name),
         email             = EXCLUDED.email,
         phone             = EXCLUDED.phone,
         website           = EXCLUDED.website,
         address           = EXCLUDED.address,
         telegram_chat_id  = COALESCE(EXCLUDED.telegram_chat_id, vendor_profiles.telegram_chat_id),
         whatsapp          = COALESCE(EXCLUDED.whatsapp, vendor_profiles.whatsapp),
         updated_at        = NOW()`,
      [w, tenantId]
    );
    return rowCount > 0;
  } finally {
    __vendorSeedGuard--;
  }
}

// Back-compat alias for old call sites
async function maybeSeedVendor(address) {
  return seedVendorFromUserProfile(pool, address, null);
}

function requireAdmin(req, res, next) {
  try {
    const token = req.headers.authorization?.startsWith('Bearer ')
      ? req.headers.authorization.slice(7)
      : req.cookies?.auth_token;
    const user = token ? verifyJwt(token) : null;
    if (!user?.sub) return res.status(401).json({ error: 'unauthenticated' });
    if (!isAdminAddress(String(user.sub).toLowerCase())) {
      return res.status(403).json({ error: 'forbidden', message: 'admin only' });
    }
    req.user = user;
    return next();
  } catch {
    return res.status(401).json({ error: 'unauthenticated' });
  }
}

// ==============================
// Config
// ==============================
const PORT = Number(process.env.PORT || 3000);
const DEFAULT_ORIGIN = "https://lithiumx.netlify.app";

const CORS_ORIGINS = (process.env.CORS_ORIGINS || process.env.CORS_ORIGIN || DEFAULT_ORIGIN)
  .split(",")
  .map((s) => s.trim())
  .filter(Boolean);

CORS_ORIGINS.push("https://sally-uyuni-855007491806.us-west1.run.app");

const PINATA_API_KEY = (process.env.PINATA_API_KEY || "").trim();
const PINATA_SECRET_API_KEY = (process.env.PINATA_SECRET_API_KEY || "").trim();
const PINATA_GATEWAY = process.env.PINATA_GATEWAY_DOMAIN || "gateway.pinata.cloud";

// Optional: dedicated gateway auth + public fallback
const PINATA_JWT = (process.env.PINATA_JWT || "").trim();                     // your Pinata JWT (works on dedicated gateways)
const PINATA_GATEWAY_TOKEN = (process.env.PINATA_GATEWAY_TOKEN || "").trim(); // or a Gateway Subdomain Token
const PINATA_PUBLIC_GATEWAY = process.env.PINATA_PUBLIC_GATEWAY || "https://gateway.pinata.cloud/ipfs/";

// OpenAI client (supports project-scoped keys)
const openai = (() => {
  const key = (process.env.OPENAI_API_KEY || "").trim();
  if (!key) return null;
  return new OpenAI({
    apiKey: key,
    project: process.env.OPENAI_PROJECT || undefined,
    organization: process.env.OPENAI_ORG || undefined,
  });
})();

// Blockchain
const SEPOLIA_RPC_URL = process.env.SEPOLIA_RPC_URL || "https://ethereum-sepolia.publicnode.com";
const PRIVATE_KEY = process.env.PRIVATE_KEY || "";

const USDC_ADDRESS = process.env.USDC_ADDRESS || "0x1c7D4B196Cb0C7B01d743Fbc6116a902379C7238";
const USDT_ADDRESS = process.env.USDT_ADDRESS || "0x7169D38820dfd117C3FA1f22a697dBA58d90BA06";

const ERC20_ABI = [
  "function transfer(address to, uint256 amount) returns (bool)",
  "function balanceOf(address account) view returns (uint256)",
  "function decimals() view returns (uint8)",
];

const TOKENS = {
  USDC: { address: USDC_ADDRESS, decimals: 6 },
  USDT: { address: USDT_ADDRESS, decimals: 6 },
};

// --- ERC20 Transfer log salvage (find tx hash if wrapper didn't return one) ---
const TRANSFER_TOPIC = ethers.utils.id("Transfer(address,address,uint256)");

async function salvageTxHashViaLogs(rpcUrl, tokenOrSymbol, toAddress, amountRaw) {
  try {
    if (!rpcUrl) return null;
    if (!toAddress) return null;

    // resolve token address from symbol or accept direct address
    let tokenAddr = tokenOrSymbol;
    if (typeof tokenOrSymbol === 'string' && !/^0x[0-9a-fA-F]{40}$/.test(tokenOrSymbol)) {
      tokenAddr = (TOKENS[tokenOrSymbol] && TOKENS[tokenOrSymbol].address) || null;
    }
    if (!tokenAddr || !/^0x[0-9a-fA-F]{40}$/.test(tokenAddr)) return null;

    const provider = new ethers.providers.JsonRpcProvider(rpcUrl);

    // decimals
    let dec = (TOKENS[tokenOrSymbol]?.decimals ?? TOKENS[tokenAddr]?.decimals);
    if (!Number.isFinite(dec)) {
      try {
        const decCtr = new ethers.Contract(tokenAddr, ERC20_ABI, provider);
        dec = await decCtr.decimals();
      } catch { dec = 6; }
    }

    const amountUnits = ethers.utils.parseUnits(String(amountRaw), dec);

    const head = await provider.getBlockNumber();
    const win = Math.max(1, Number(process.env.SALVAGE_BLOCK_WINDOW || 6000)); // ~20–30min window
    const fromBlock = Math.max(0, head - win);

    const topicTo = ethers.utils.hexZeroPad(ethers.utils.getAddress(toAddress), 32);
    const logs = await provider.getLogs({
      address: ethers.utils.getAddress(tokenAddr),
      fromBlock,
      toBlock: 'latest',
      topics: [TRANSFER_TOPIC, null, topicTo],
    });

    // newest first; match exact amount
    for (let i = logs.length - 1; i >= 0; i--) {
      const log = logs[i];
      const val = ethers.BigNumber.from(log.data); // amount
      if (val.eq(amountUnits)) {
        return log.transactionHash;
      }
    }
    return null;
  } catch (e) {
    console.warn('[SALVAGE] failed:', e?.message || e);
    return null;
  }
}

// ==============================
// Database
// ==============================
const pool = new Pool({
  connectionString: process.env.DATABASE_URL,
  ssl: { rejectUnauthorized: false },
});

(async () => {
  try {
    if (typeof ensureUserProfilesSchema === 'function') {
      await ensureUserProfilesSchema();
    } else {
      console.warn('[startup] ensureUserProfilesSchema is not defined — skipping schema bootstrap');
    }
  } catch (e) {
    console.error('[startup] ensureUserProfilesSchema failed', e);
  }
})();

// Ensures the vendor/user profiles table and columns exist.
// Safe to run at every boot.
async function ensureUserProfilesSchema() {
  const sql = `
    CREATE TABLE IF NOT EXISTS vendor_profiles (
      profile_id SERIAL PRIMARY KEY,
      wallet_address TEXT UNIQUE NOT NULL,
      vendor_name   TEXT,
      email         TEXT,
      phone         TEXT,
      website       TEXT,
      address       TEXT,
      profile       JSONB DEFAULT '{}'::jsonb,
      created_at    TIMESTAMPTZ DEFAULT now(),
      updated_at    TIMESTAMPTZ DEFAULT now()
    );

    -- Redundant address key often used by the UI
    ALTER TABLE vendor_profiles
      ADD COLUMN IF NOT EXISTS address1 TEXT;

    -- Keep both top-level and nested profile forms available to the UI
    -- (No-op if rows already present; this just standardizes shape for new inserts)
  `;
  await pool.query(sql);
  console.log('[startup] vendor_profiles schema ensured');
}

// ---- Safe Tx overlay helpers (response-time hydration) ----
const SAFE_CACHE_TTL_MS = Number(process.env.SAFE_CACHE_TTL_MS || 5000);

const SAFE_LOOKUPS_PER_REQUEST =
  process.env.SAFE_LOOKUPS_PER_REQUEST !== undefined
    ? Math.max(0, Math.floor(Number(process.env.SAFE_LOOKUPS_PER_REQUEST)))
    : 8;

const _safeStatusCache = new Map(); // key: safeTxHash -> { at, isExecuted, txHash }

const _safeTxUrlBase = (process.env.SAFE_TXSERVICE_URL || 'https://api.safe.global/tx-service/eth')
  .trim()
  .replace(/\/+$/, '');

async function _getSafeTxStatus(safeTxHash) {
  const now = Date.now();
  const cached = _safeStatusCache.get(safeTxHash);
  if (cached && now - cached.at < SAFE_CACHE_TTL_MS) return cached;

  const url = `${_safeTxUrlBase}/api/v1/multisig-transactions/${safeTxHash}`;
  const headers = process.env.SAFE_API_KEY ? { Authorization: `Bearer ${process.env.SAFE_API_KEY}` } : {};
  const fetcher = (typeof safeFetchRL === 'function') ? safeFetchRL : fetch;

  try {
    const r = await fetcher(url, { headers });
    if (!r.ok) throw new Error(String(r.status));
    const t = await r.json();

    const statusStr = String(t?.tx_status || t?.status || "").toLowerCase();
    const out = {
      at: now,
      isExecuted:
        !!t?.is_executed ||
        !!t?.isExecuted ||
        !!t?.execution_date ||
        !!t?.executionDate ||
        !!t?.transaction_hash ||
        statusStr === 'success' || statusStr === 'executed' || statusStr === 'successful',
      txHash: t?.transaction_hash || t?.tx_hash || t?.transactionHash || null,
    };
    _safeStatusCache.set(safeTxHash, out);
    return out;
  } catch {
    const out = { at: now, isExecuted: false, txHash: null };
    _safeStatusCache.set(safeTxHash, out);
    return out;
  }
}

// NEW: If a different SafeTx at the same NONCE got executed (rebroadcast), find it
async function _findExecutedByNonce(nonce) {
  if (nonce === null || nonce === undefined) return null;

  const SAFE_ADDRESS = (process.env.SAFE_ADDRESS || process.env.SAFE_WALLET || '').trim();
  if (!SAFE_ADDRESS) return null;

  const url = `${_safeTxUrlBase}/api/v1/safes/${SAFE_ADDRESS}/multisig-transactions/?nonce=${Number(nonce)}&ordering=-submissionDate&limit=10`;
  const headers = process.env.SAFE_API_KEY ? { Authorization: `Bearer ${process.env.SAFE_API_KEY}` } : {};
  const fetcher = (typeof safeFetchRL === 'function') ? safeFetchRL : fetch;

  try {
    const r = await fetcher(url, { headers });
    if (!r.ok) return null;
    const j = await r.json();

    const hit = (j?.results || []).find(t =>
      t?.is_executed || t?.isExecuted || t?.transaction_hash || t?.transactionHash || t?.execution_date || t?.executionDate
    );
    if (!hit) return null;

    return {
      safeTxHash: hit.safe_tx_hash || hit.safeTxHash,
      isExecuted: true,
      txHash: hit.transaction_hash || hit.tx_hash || hit.transactionHash || null,
    };
  } catch {
    return null;
  }
}

// Finalize DB (fire-and-forget)
async function _finalizePaidInDb({ bidId, milestoneIndex, txHash, safeTxHash, tenantId }) {
  try {
    // Update milestone JSON
    const { rows: b } = await pool.query('SELECT milestones FROM bids WHERE bid_id=$1 AND tenant_id=$2', [bidId, tenantId]);
    if (!b[0]) return;
    const arr = Array.isArray(b[0].milestones) ? b[0].milestones : JSON.parse(b[0].milestones || '[]');
    const ms = { ...(arr[milestoneIndex] || {}) };
    const iso = new Date().toISOString();

    if (safeTxHash && !ms.safePaymentTxHash) ms.safePaymentTxHash = safeTxHash;
    ms.paymentTxHash = ms.paymentTxHash || txHash || null;
    ms.paymentDate = ms.paymentDate || iso;
    ms.paidAt = ms.paidAt || ms.paymentDate;
    ms.paymentPending = false;
    ms.status = 'paid';

    arr[milestoneIndex] = ms;
    await pool.query('UPDATE bids SET milestones=$1 WHERE bid_id=$2 AND tenant_id=$3', [JSON.stringify(arr), bidId, tenantId]);

    // Update milestone_payments (also switch to the new safe_tx_hash if the hash changed)
    await pool.query(
      `UPDATE milestone_payments
         SET status='released',
             safe_tx_hash = COALESCE($4, safe_tx_hash),
             tx_hash=COALESCE($3, tx_hash),
             released_at=COALESCE(released_at, NOW())
       WHERE bid_id=$1 AND milestone_index=$2 AND tenant_id=$5`,
      [bidId, milestoneIndex, txHash || null, safeTxHash || null, tenantId]
    );
  } catch (e) {
    console.warn('[overlay finalize] DB finalize failed', e?.message || e);
  }
}

// --- Overlay "Paid" status from milestone_payments into bid.milestones for responses ---
// server.js

async function overlayPaidFromMp(bid, pool) {
  const bidId = bid.bid_id ?? bid.bidId;
  if (!bidId) return bid;

  let msArr = Array.isArray(bid.milestones)
    ? bid.milestones
    : JSON.parse(bid.milestones || '[]');

  // get the newest row per milestone_index
  const { rows: mpRows } = await pool.query(
    `SELECT DISTINCT ON (milestone_index)
           milestone_index, status, tx_hash, safe_tx_hash, released_at, safe_nonce, created_at, id
       FROM milestone_payments
      WHERE bid_id = $1 AND tenant_id = $2
      ORDER BY milestone_index, created_at DESC, id DESC`,
    [bidId, bid.tenant_id]
  );

  // Create a map for O(1) lookup
  const byIdx = new Map(mpRows.map(r => [Number(r.milestone_index), r]));

  // Pass 1: Rebuild status based strictly on milestone_payments table
  for (let i = 0; i < msArr.length; i++) {
    const r = byIdx.get(i);

    // If no payment row exists in DB, clear any stuck "Pending" flag from the JSON
    if (!r) {
      if (msArr[i].paymentPending) {
        msArr[i] = { ...msArr[i], paymentPending: false };
      }
      continue;
    }

    const s = String(r.status || '').toLowerCase();
    // FIX: Use tx_hash existence as the source of truth
    const hasTx = !!r.tx_hash && r.tx_hash.length > 10;
    const alreadyReleased = s === 'released' || hasTx || !!r.released_at;

    if (alreadyReleased) {
      const paidIso = r.released_at
        ? new Date(r.released_at).toISOString()
        : new Date().toISOString();

      msArr[i] = {
        ...(msArr[i] || {}),
        paymentTxHash: msArr[i]?.paymentTxHash || r.tx_hash || null,
        safePaymentTxHash: msArr[i]?.safePaymentTxHash || r.safe_tx_hash || null,
        paymentDate: msArr[i]?.paymentDate || paidIso,
        paidAt: msArr[i]?.paidAt || paidIso,
        paymentPending: false, // <--- FORCE CLEAR
        status: 'paid',
      };
    } else if (s === 'pending') {
      // It is genuinely pending in the DB (no tx hash yet)
      msArr[i].paymentPending = true;
    }
  }

  // ... (Keep the rest of Pass 2 Safe Logic exactly as it was) ...
  // Build list of still-pending-with-safe rows
  let lookupsLeft =
    process.env.SAFE_LOOKUPS_PER_REQUEST !== undefined
      ? Math.max(0, Math.floor(Number(process.env.SAFE_LOOKUPS_PER_REQUEST)))
      : 8; // (SAFE_LOOKUPS_PER_REQUEST default)

  const pending = mpRows
    .filter(r => {
      const s = String(r.status || '').toLowerCase();
      const hasTx = !!r.tx_hash && r.tx_hash.length > 10;
      const alreadyReleased = s === 'released' || hasTx || !!r.released_at;
      return !alreadyReleased && r.safe_tx_hash != null;
    })
    .sort((a, b) => new Date(b.created_at || 0) - new Date(a.created_at || 0));

  const tasks = [];
  for (const r of pending) {
    if (lookupsLeft <= 0) break;
    lookupsLeft--;

    const idx = Number(r.milestone_index);
    if (!Number.isFinite(idx)) continue;

    const safeHash = r.safe_tx_hash;
    const nonce = r.safe_nonce ?? null;
    const tenantId = bid.tenant_id; // Extract tenantId from bid

    tasks.push((async () => {
      const st = await _getSafeTxStatus(safeHash);
      if (st?.isExecuted) {
        const iso = new Date().toISOString();
        msArr[idx] = {
          ...(msArr[idx] || {}),
          paymentTxHash: msArr[idx]?.paymentTxHash || st.txHash || null,
          safePaymentTxHash: msArr[idx]?.safePaymentTxHash || safeHash,
          paymentDate: msArr[idx]?.paymentDate || iso,
          paidAt: msArr[idx]?.paidAt || iso,
          paymentPending: false,
          status: 'paid',
        };
        await _finalizePaidInDb({ bidId, milestoneIndex: idx, txHash: st.txHash, safeTxHash: safeHash, tenantId });
        return;
      }

      const alt = await _findExecutedByNonce(nonce);
      if (alt?.isExecuted) {
        const iso = new Date().toISOString();
        msArr[idx] = {
          ...(msArr[idx] || {}),
          paymentTxHash: msArr[idx]?.paymentTxHash || alt.txHash || null,
          safePaymentTxHash: msArr[idx]?.safePaymentTxHash || alt.safeTxHash,
          paymentDate: msArr[idx]?.paymentDate || iso,
          paidAt: msArr[idx]?.paidAt || iso,
          paymentPending: false,
          status: 'paid',
        };
        await _finalizePaidInDb({ bidId, milestoneIndex: idx, txHash: alt.txHash, safeTxHash: alt.safeTxHash, tenantId });
        return;
      }

      // Still pending
      msArr[idx] = {
        ...(msArr[idx] || {}),
        safePaymentTxHash: msArr[idx]?.safePaymentTxHash || safeHash,
        safeTxHash: msArr[idx]?.safeTxHash || safeHash,
        safeNonce: msArr[idx]?.safeNonce ?? nonce,
        safeStatus: msArr[idx]?.safeStatus || 'submitted',
        paymentPending: true,
      };
    })());
  }

  if (tasks.length) await Promise.all(tasks);

  return { ...bid, milestones: msArr };
}

// ---- Enrich bids with payment state from milestone_payments
async function attachPaymentState(bids) {
  if (!Array.isArray(bids) || bids.length === 0) return bids;

  // Handle both snake_case and camelCase bid ids
  const bidIds = bids
    .map(b => Number(b.bidId ?? b.bid_id))
    .filter(Boolean);

  if (bidIds.length === 0) return bids;

  const { rows: payRows } = await pool.query(
    `SELECT bid_id, milestone_index, status, tx_hash
       FROM milestone_payments
      WHERE bid_id = ANY($1::bigint[]) AND tenant_id = $2`,
    [bidIds, bids[0].tenant_id]
  );

  const byKey = new Map();
  for (const r of payRows) {
    byKey.set(`${Number(r.bid_id)}:${Number(r.milestone_index)}`, r);
  }

  return bids.map(b => {
    const bidId = Number(b.bidId ?? b.bid_id);
    let milestones = Array.isArray(b.milestones)
      ? b.milestones
      : JSON.parse(b.milestones || '[]');

    milestones = milestones.map((m, i) => {
      const hit = byKey.get(`${bidId}:${i}`);
      if (!hit) return m;

      // FIX: Check if tx_hash is missing. If a hash exists, treat it as released/paid.
      if (hit.status === 'pending' && !hit.tx_hash) {
        // show the amber "Payment Pending" pill and hide the green button
        return { ...m, paymentPending: true };
      }

      // If released OR if we have a tx_hash (even if status is pending)
      if (hit.status === 'released' || hit.tx_hash) {
        // make sure the UI sees it as paid
        const tx = hit.tx_hash || m.paymentTxHash || null;
        return { ...m, paymentTxHash: tx, paid: true, paymentPending: false };
      }
      return m;
    });

    // Preserve original shape (camel or snake)
    if ('bidId' in b) {
      return { ...b, milestones };
    } else {
      return { ...b, milestones }; // if you normally stringify, do it in the route before res.json
    }
  });
}

// ==============================
// DB bootstrap — vendor_profiles (create if missing)
// ==============================
(async () => {
  try {
    await pool.query(`
      CREATE TABLE IF NOT EXISTS vendor_profiles (
        wallet_address   text PRIMARY KEY,
        vendor_name      text NOT NULL,
        email            text,
        phone            text,
        address          text,
        website          text,
        archived         boolean NOT NULL DEFAULT false,  -- NEW
        telegram_chat_id text,                            -- NEW
        created_at       timestamptz NOT NULL DEFAULT now(),
        updated_at       timestamptz NOT NULL DEFAULT now()
      );
    `);

    // In case the table already existed without the columns
    await pool.query(`ALTER TABLE vendor_profiles ADD COLUMN IF NOT EXISTS archived boolean NOT NULL DEFAULT false;`);
    await pool.query(`ALTER TABLE vendor_profiles ADD COLUMN IF NOT EXISTS telegram_chat_id text;`);

    await pool.query(`
      CREATE INDEX IF NOT EXISTS idx_vendor_profiles_name
      ON vendor_profiles (lower(vendor_name));
    `);
    await pool.query(`CREATE INDEX IF NOT EXISTS idx_vendor_profiles_archived ON vendor_profiles (archived);`);

    console.log('[db] vendor_profiles ready');
  } catch (e) {
    console.error('vendor_profiles init failed:', e);
  }
})();


(async function initDb() {
  try {

    // Generic user profile (shared fields before picking a role)
    await pool.query(`
  CREATE TABLE IF NOT EXISTS user_profiles (
    wallet_address TEXT PRIMARY KEY,
    display_name   TEXT,
    email          TEXT,
    phone          TEXT,
    website        TEXT,
    address        TEXT,
    city           TEXT,
    country        TEXT,
    telegram_chat_id TEXT,
    whatsapp       TEXT,
    updated_at     TIMESTAMP DEFAULT NOW()
  );
`);
    console.log('[db] user_profiles ready');

    await pool.query(`
  CREATE TABLE IF NOT EXISTS proposer_profiles (
    wallet_address   TEXT PRIMARY KEY,
    org_name         TEXT,
    contact_email    TEXT,
    phone            TEXT,
    website          TEXT,
    address          TEXT,
    city             TEXT,
    country          TEXT,
    telegram_chat_id TEXT,
    whatsapp         TEXT,
    status           TEXT DEFAULT 'active',  -- active|archived
    created_at       TIMESTAMP DEFAULT NOW(),
    updated_at       TIMESTAMP DEFAULT NOW()
  );
`);

    await pool.query(`ALTER TABLE user_profiles ADD COLUMN IF NOT EXISTS vendor_name TEXT`);
    // --- INSERT START: Sally Uyuni App Tables ---
    await pool.query(`
      CREATE TABLE IF NOT EXISTS school_reports (
        report_id      TEXT PRIMARY KEY,
        school_name    TEXT,
        description    TEXT,
        rating         INTEGER,
        image_cid      TEXT,
        image_url      TEXT,
        ai_analysis    JSONB,
        location       JSONB,
        wallet_address TEXT,
        created_at     TIMESTAMPTZ DEFAULT NOW()
      );
    `);
    console.log('[db] school_reports ready');
    // --- INSERT END ---
    await pool.query(`ALTER TABLE user_profiles ADD COLUMN IF NOT EXISTS telegram_username TEXT`);
    await pool.query(`ALTER TABLE proposer_profiles ADD COLUMN IF NOT EXISTS telegram_username TEXT`);

    console.log('[db] proposer_profiles ready');
  } catch (e) {
    console.error('[initDb] error', e);
  }
})();

// ==============================
// DB bootstrap — proposals owner fields (create if missing)
// ==============================
(async () => {
  try {
    // Add columns if they don't exist
    await pool.query(`
      ALTER TABLE proposals
        ADD COLUMN IF NOT EXISTS owner_wallet              text,
        ADD COLUMN IF NOT EXISTS owner_email               text,
        ADD COLUMN IF NOT EXISTS owner_phone               text,               -- NEW
        ADD COLUMN IF NOT EXISTS owner_telegram_chat_id    text,               -- NEW
        ADD COLUMN IF NOT EXISTS updated_at                timestamptz NOT NULL DEFAULT now();
    `);

    // Helpful index for "my proposals"
    await pool.query(`
      CREATE INDEX IF NOT EXISTS idx_proposals_owner_wallet
      ON proposals (lower(owner_wallet));
    `);

    console.log('[db] proposals owner fields ready');
  } catch (e) {
    console.error('proposals owner fields init failed:', e);
  }
})();

// --- DB MIGRATION: Add location column to proposals ---
(async () => {
  try {
    await pool.query(`
      ALTER TABLE proposals
      ADD COLUMN IF NOT EXISTS location JSONB;
    `);
    console.log('[db] Successfully added "location" column to proposals table');
  } catch (e) {
    console.error('[db] Failed to add location column:', e);
  }
})();



(async () => {
  try {
    await pool.query(`
      CREATE TABLE IF NOT EXISTS bid_audits (
        id            bigserial PRIMARY KEY,
        bid_id        bigint NOT NULL,
        actor_wallet  text,
        actor_role    text,
        changes       jsonb NOT NULL,
        created_at    timestamptz NOT NULL DEFAULT now()
      );
    `);
    await pool.query(`CREATE INDEX IF NOT EXISTS idx_bid_audits_bid ON bid_audits (bid_id);`);
    console.log('[db] bid_audits ready');
  } catch (e) {
    console.error('bid_audits init failed:', e);
  }
})();

// ==============================
// DB bootstrap — required columns for proofs/bids used below
// ==============================
(async () => {
  try {
    await pool.query(`
      ALTER TABLE proofs
        ADD COLUMN IF NOT EXISTS file_meta     jsonb,
        ADD COLUMN IF NOT EXISTS gps_lat       double precision,
        ADD COLUMN IF NOT EXISTS gps_lon       double precision,
        ADD COLUMN IF NOT EXISTS gps_alt       double precision,
        ADD COLUMN IF NOT EXISTS capture_time  timestamptz,
        ADD COLUMN IF NOT EXISTS vendor_prompt text,
        ADD COLUMN IF NOT EXISTS updated_at    timestamptz NOT NULL DEFAULT now();
    `);
    await pool.query(`
      ALTER TABLE bids
        ADD COLUMN IF NOT EXISTS updated_at    timestamptz NOT NULL DEFAULT now(),
        ADD COLUMN IF NOT EXISTS files         jsonb;
    `);
    console.log('[db] proofs/bids columns ready');
  } catch (e) {
    console.error('proofs/bids columns init failed:', e);
  }
})();

// ==============================
// DB bootstrap — proofs decision columns (approve/reject)
// ==============================
(async () => {
  try {
    await pool.query(`
      ALTER TABLE proofs
        ADD COLUMN IF NOT EXISTS approved_at   timestamptz,
        ADD COLUMN IF NOT EXISTS approved_by   text,
        ADD COLUMN IF NOT EXISTS rejected_at   timestamptz,
        ADD COLUMN IF NOT EXISTS rejected_by   text,
        ADD COLUMN IF NOT EXISTS decision_note text
    `);
    console.log('[db] proofs decision columns ready');
  } catch (e) {
    console.error('proofs decision cols init failed:', e);
  }
})();

// ==============================
// DB bootstrap — dashboard state for "what's new" widget
// ==============================
(async () => {
  try {
    await pool.query(`
      CREATE TABLE IF NOT EXISTS user_dashboard_state (
        wallet_address   text PRIMARY KEY,
        last_seen_digest timestamptz NOT NULL DEFAULT now(),
        updated_at       timestamptz NOT NULL DEFAULT now()
      );
    `);
    await pool.query(`
      CREATE INDEX IF NOT EXISTS idx_user_dash_updated
      ON user_dashboard_state (updated_at DESC);
    `);
    console.log('[db] user_dashboard_state ready');
  } catch (e) {
    console.error('user_dashboard_state init failed:', e);
  }
})();

// ==============================
// DB cleanup: collapse duplicate PENDING proofs per (bid, milestone) to the latest
// and then enforce "at most one PENDING" going forward.
// ==============================
(async () => {
  try {
    // 1) If there are multiple PENDING proofs for the same milestone,
    //    keep the latest and mark the rest REJECTED.
    await pool.query(`
      WITH ranked AS (
        SELECT proof_id,
               ROW_NUMBER() OVER (
                 PARTITION BY bid_id, milestone_index
                 ORDER BY submitted_at DESC NULLS LAST,
                          updated_at  DESC NULLS LAST,
                          proof_id    DESC
               ) AS rn
        FROM proofs
        WHERE status = 'pending'
      )
      UPDATE proofs p
         SET status = 'rejected',
             updated_at = NOW()
      FROM ranked r
      WHERE p.proof_id = r.proof_id
        AND r.rn > 1
    `);

    // 2) Enforce "only one PENDING per (bid_id, milestone_index)" going forward.
    await pool.query(`
      CREATE UNIQUE INDEX IF NOT EXISTS ux_proofs_pending
        ON proofs (bid_id, milestone_index)
      WHERE status = 'pending';
    `);

    console.log('[db] duplicate pending proofs cleaned; unique index ready');
  } catch (e) {
    console.error('DB cleanup/index for proofs failed:', e);
  }
})();

// ==============================
// DB bootstrap — templates marketplace
// ==============================
(async () => {
  try {
    await pool.query(`
      CREATE TABLE IF NOT EXISTS templates (
        template_id       bigserial PRIMARY KEY,
        slug              text UNIQUE NOT NULL,
        title             text NOT NULL,
        locale            text DEFAULT 'en',
        category          text,
        summary           text,
        default_currency  text DEFAULT 'USD',
        created_at        timestamptz NOT NULL DEFAULT now(),
        updated_at        timestamptz NOT NULL DEFAULT now()
      );
    `);

    await pool.query(`
      CREATE TABLE IF NOT EXISTS template_milestones (
        id           bigserial PRIMARY KEY,
        template_id  bigint NOT NULL REFERENCES templates(template_id) ON DELETE CASCADE,
        idx          integer NOT NULL,
        name         text NOT NULL,
        amount       numeric NOT NULL DEFAULT 0,
        days_offset  integer NOT NULL DEFAULT 30,
        acceptance   jsonb DEFAULT '[]'::jsonb
      );
    `);

    await pool.query(`CREATE UNIQUE INDEX IF NOT EXISTS ux_template_ms ON template_milestones(template_id, idx);`);
    console.log('[db] templates ready');
  } catch (e) {
    console.error('templates init failed:', e?.message || e);
  }
})();

// ==============================
// DB bootstrap — Multi-Tenancy (Tenants, Configs, Members)
// ==============================
(async () => {
  try {
    // 1. Tenants Table
    await pool.query(`
      CREATE TABLE IF NOT EXISTS tenants (
        id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
        name TEXT NOT NULL,
        slug TEXT UNIQUE NOT NULL,
        created_at TIMESTAMPTZ DEFAULT NOW(),
        updated_at TIMESTAMPTZ DEFAULT NOW()
      );
    `);

    // 2. Tenant Configs (Encrypted Credentials)
    await pool.query(`
      CREATE TABLE IF NOT EXISTS tenant_configs (
        id SERIAL PRIMARY KEY,
        tenant_id UUID NOT NULL REFERENCES tenants(id) ON DELETE CASCADE,
        key TEXT NOT NULL,
        value TEXT NOT NULL,
        is_encrypted BOOLEAN DEFAULT FALSE,
        created_at TIMESTAMPTZ DEFAULT NOW(),
        updated_at TIMESTAMPTZ DEFAULT NOW(),
        UNIQUE(tenant_id, key)
      );
    `);

    // 3. Tenant Members (User Roles within a Tenant)
    await pool.query(`
      CREATE TABLE IF NOT EXISTS tenant_members (
        id SERIAL PRIMARY KEY,
        tenant_id UUID NOT NULL REFERENCES tenants(id) ON DELETE CASCADE,
        wallet_address TEXT NOT NULL,
        role TEXT NOT NULL, -- 'admin', 'vendor', 'proposer'
        created_at TIMESTAMPTZ DEFAULT NOW(),
        UNIQUE(tenant_id, wallet_address)
      );
    `);

    // 4. Add tenant_id to existing tables
    const tables = ['proposals', 'bids', 'proofs', 'vendor_profiles', 'proposer_profiles', 'school_reports', 'user_dashboard_state', 'milestone_payments'];
    for (const table of tables) {
      await pool.query(`
        ALTER TABLE ${table}
        ADD COLUMN IF NOT EXISTS tenant_id UUID REFERENCES tenants(id);
      `);
    }

    // 5. Create Default Tenant (if none exists) & Migrate Data
    // We use a specific UUID for the default tenant to make migration idempotent
    const defaultTenantId = '00000000-0000-0000-0000-000000000000';

    // Insert default tenant if not exists
    await pool.query(`
      INSERT INTO tenants (id, name, slug)
      VALUES ($1, 'Global', 'default')
      ON CONFLICT (id) DO NOTHING;
    `, [defaultTenantId]);

    // Backfill NULL tenant_ids with default tenant
    for (const table of tables) {
      await pool.query(`
        UPDATE ${table}
        SET tenant_id = $1
        WHERE tenant_id IS NULL;
      `, [defaultTenantId]);
    }

    // 6. Special Handling: user_dashboard_state PK update
    // (Safe to run after backfill because tenant_id is now populated)
    await pool.query(`
      ALTER TABLE user_dashboard_state DROP CONSTRAINT IF EXISTS user_dashboard_state_pkey;
    `);
    await pool.query(`
      ALTER TABLE user_dashboard_state ADD PRIMARY KEY (wallet_address, tenant_id);
    `);

    console.log('[db] multi-tenancy schema ready & migrated');
  } catch (e) {
    console.error('multi-tenancy init failed:', e?.message || e);
  }
})();

// ==============================
// Utilities
// ==============================
function toCamel(row) {
  if (!row || typeof row !== "object") return row;
  const out = {};
  for (const key of Object.keys(row)) {
    const camel = key.replace(/_([a-z])/g, (_, c) => c.toUpperCase());
    out[camel] = row[key];
  }
  return out;
}
function mapRows(rows) { return rows.map(toCamel); }
function coerceJson(val) {
  if (!val) return null;
  if (typeof val === "string") {
    try { return JSON.parse(val); } catch { return null; }
  }
  return val;
}

// ==============================
// Notifications (Telegram, Email via Resend, WhatsApp via Twilio)
// ==============================
const RESEND_API_KEY = process.env.RESEND_API_KEY || "";
// Accept either RESEND_FROM or MAIL_FROM (backward compatible)
const MAIL_FROM = process.env.RESEND_FROM || process.env.MAIL_FROM || "LithiumX <noreply@example.com>";
// Optional Reply-To (works with either RESEND_REPLY_TO or MAIL_REPLY_TO)
const MAIL_REPLY_TO = process.env.RESEND_REPLY_TO || process.env.MAIL_REPLY_TO || undefined;

const MAIL_ADMIN_TO = (process.env.MAIL_ADMIN_TO || "")
  .split(",")
  .map(s => s.trim())
  .filter(Boolean);

const TELEGRAM_BOT_TOKEN = process.env.TELEGRAM_BOT_TOKEN || "";
const TELEGRAM_ADMIN_CHAT_IDS = (process.env.TELEGRAM_ADMIN_CHAT_IDS || "")
  .split(",")
  .map(s => s.trim())
  .filter(Boolean);

const TWILIO_ACCOUNT_SID = process.env.TWILIO_ACCOUNT_SID || "";
const TWILIO_AUTH_TOKEN = process.env.TWILIO_AUTH_TOKEN || "";
const TWILIO_WHATSAPP_FROM = process.env.TWILIO_WHATSAPP_FROM || "";
const ADMIN_WHATSAPP = (process.env.ADMIN_WHATSAPP || "")
  .split(",")
  .map(s => s.trim())
  .filter(Boolean);
const TWILIO_WA_CONTENT_SID = process.env.TWILIO_WA_CONTENT_SID || "";

const APP_BASE_URL = process.env.APP_BASE_URL || process.env.NEXT_PUBLIC_APP_BASE_URL || "";
const NOTIFY_ENABLED = String(process.env.NOTIFY_ENABLED || "true").toLowerCase() !== "false";
const NOTIFY_CONF_THRESHOLD = Number(process.env.NOTIFY_CONF_THRESHOLD || 0.35);
const WA_DEFAULT_COUNTRY = process.env.WA_DEFAULT_COUNTRY || "+1";

// ---- Safe stub so accidental calls don't crash if the real function isn't defined
const notifyVendorSignupVendor =
  (typeof globalThis.notifyVendorSignupVendor === 'function')
    ? globalThis.notifyVendorSignupVendor
    : async function noopNotifyVendorSignupVendor() { /* no-op */ };

// Small helpers
function toE164(raw) {
  if (!raw) return null;
  const s = String(raw).replace(/[^\d+]/g, "");
  if (s.startsWith("+")) return s;
  return `${WA_DEFAULT_COUNTRY}${s}`;
}

// Determine role from address: admin > vendor (has vendor_profile) > entity (has proposals) > user
async function roleForAddress(address) {
  if (isAdminAddress(address)) return 'admin';

  // vendor if has a vendor profile
  const { rows: vp } = await pool.query(
    `SELECT 1 FROM vendor_profiles WHERE lower(wallet_address)=lower($1) LIMIT 1`,
    [address]
  );
  if (vp[0]) return 'vendor';

  // entity if has at least one proposal they own
  const { rows: ep } = await pool.query(
    `SELECT 1 FROM proposals WHERE lower(owner_wallet)=lower($1) LIMIT 1`,
    [address]
  );
  if (ep[0]) return 'entity';

  return 'user';
}

// Telegram
async function sendTelegram(chatIds, text) {
  if (!TELEGRAM_BOT_TOKEN || !chatIds?.length) return;
  const payloads = chatIds.map(chat_id => ({
    method: "POST",
    url: `https://api.telegram.org/bot${TELEGRAM_BOT_TOKEN}/sendMessage`,
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ chat_id, text, parse_mode: "HTML", disable_web_page_preview: true }),
  }));
  await Promise.all(payloads.map(p => sendRequest("POST", p.url, p.headers, p.body).catch(() => null)));
}

// Email (Resend)
async function sendEmail(toList, subject, html) {
  if (!RESEND_API_KEY || !toList?.length) return;
  const payload = JSON.stringify({
    from: MAIL_FROM,
    to: toList,
    subject,
    html,
    reply_to: MAIL_REPLY_TO,   // <— added line
  });
  await sendRequest(
    "POST",
    "https://api.resend.com/emails",
    { "Authorization": `Bearer ${RESEND_API_KEY}`, "Content-Type": "application/json" },
    payload
  );
}

// always force a proper WhatsApp address: whatsapp:+E164
function ensureWaAddr(x) {
  const s = String(x || '').trim();
  if (s.toLowerCase().startsWith('whatsapp:')) {
    const num = s.slice(9).replace(/[^\d+]/g, '');
    return `whatsapp:${num.startsWith('+') ? num : `+${num}`}`;
  }
  const digits = s.replace(/[^\d+]/g, '');
  const e164 = digits.startsWith('+') ? digits : `+${digits}`;
  return `whatsapp:${e164}`;
}

// WhatsApp (Twilio)
async function sendWhatsApp(to, body) {
  if (!TWILIO_ACCOUNT_SID || !TWILIO_AUTH_TOKEN || !TWILIO_WHATSAPP_FROM) return;

  const fromAddr = ensureWaAddr(TWILIO_WHATSAPP_FROM); // e.g. whatsapp:+1415XXXXXXX
  const toAddr = ensureWaAddr(to);                   // e.g. whatsapp:+49XXXXXXXXX

  const creds = Buffer.from(`${TWILIO_ACCOUNT_SID}:${TWILIO_AUTH_TOKEN}`).toString("base64");
  const form = new URLSearchParams({ From: fromAddr, To: toAddr, Body: body }).toString();

  await sendRequest(
    "POST",
    `https://api.twilio.com/2010-04-01/Accounts/${TWILIO_ACCOUNT_SID}/Messages.json`,
    {
      "Authorization": `Basic ${creds}`,
      "Content-Type": "application/x-www-form-urlencoded"
    },
    form
  );
}

// WhatsApp (Twilio) — Template sender (for business-initiated/out-of-session)
async function sendWhatsAppTemplate(to, contentSid, vars) {
  if (!TWILIO_ACCOUNT_SID || !TWILIO_AUTH_TOKEN || !TWILIO_WHATSAPP_FROM || !contentSid) return;

  const fromAddr = ensureWaAddr(TWILIO_WHATSAPP_FROM);
  const toAddr = ensureWaAddr(to);

  const creds = Buffer.from(`${TWILIO_ACCOUNT_SID}:${TWILIO_AUTH_TOKEN}`).toString("base64");
  const form = new URLSearchParams({
    From: fromAddr,
    To: toAddr,
    ContentSid: contentSid,
    ContentVariables: JSON.stringify(vars),
  }).toString();

  await sendRequest(
    "POST",
    `https://api.twilio.com/2010-04-01/Accounts/${TWILIO_ACCOUNT_SID}/Messages.json`,
    {
      "Authorization": `Basic ${creds}`,
      "Content-Type": "application/x-www-form-urlencoded"
    },
    form
  );
}

// Notify admins + vendor (EN + ES) when a *new* vendor signs up
// NOTE: add optional vendorTelegramChatId / vendorWhatsapp if you have them; phone is used for WA fallback.
async function notifyVendorSignup({
  wallet,
  vendorName,
  email,
  phone,
  vendorTelegramChatId = null,   // <-- pass if you have it
  vendorWhatsapp = null          // <-- pass if you have it; else phone is used
}) {
  if (!NOTIFY_ENABLED) return;

  // ---------- ADMIN (EN/ES) ----------
  const adminLink = APP_BASE_URL ? `${APP_BASE_URL}/admin/vendors` : null;

  const enLines = [
    '🆕 Vendor signup — approval needed',
    `Wallet: ${wallet}`,
    vendorName ? `Name: ${vendorName}` : null,
    email ? `Email: ${email}` : null,
    phone ? `Phone: ${phone}` : null,
    adminLink ? `Admin: ${adminLink}` : null,
  ].filter(Boolean);

  const esLines = [
    '🆕 Registro de proveedor — se requiere aprobación',
    `Billetera: ${wallet}`,
    vendorName ? `Nombre: ${vendorName}` : null,
    email ? `Correo electrónico: ${email}` : null,
    phone ? `Teléfono: ${phone}` : null,
    adminLink ? `Panel de administración: ${adminLink}` : null,
  ].filter(Boolean);

  const en = enLines.join('\n');
  const es = esLines.join('\n');
  const { text: adminText, html: adminHtml } = bi(en, es);

  await Promise.allSettled([
    TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, adminText) : null,
    MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, 'Vendor signup — approval needed', adminHtml) : null,
    ...(ADMIN_WHATSAPP || []).map(n =>
      TWILIO_WA_CONTENT_SID
        ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": vendorName || "", "2": "vendor signup" })
        : sendWhatsApp(n, adminText)
    ),
  ].filter(Boolean));

  // ---------- VENDOR (EN/ES) ----------
  const vEn = [
    'Thanks for signing up as a vendor.',
    'Your account is pending admin approval.',
    'You will receive a notification once it is approved.',
  ].join('\n');

  const vEs = [
    'Gracias por registrarte como proveedor.',
    'Tu cuenta está pendiente de aprobación por parte del administrador.',
    'Recibirás una notificación cuando sea aprobada.',
  ].join('\n');

  const { text: vendorText, html: vendorHtml } = bi(vEn, vEs);

  // Resolve WhatsApp: prefer vendorWhatsapp, else phone
  const waRaw = vendorWhatsapp || phone || null;
  const waE164 = waRaw ? toE164(waRaw) : null;

  await Promise.allSettled([
    // Email to vendor
    email ? sendEmail([email],
      'Vendor signup received — pending approval / Registro recibido — pendiente de aprobación',
      vendorHtml
    ) : null,

    // Telegram to vendor (only if you have their chat id)
    vendorTelegramChatId ? sendTelegram([vendorTelegramChatId], vendorText) : null,

    // WhatsApp to vendor (uses template if available, else plain text)
    waE164
      ? (TWILIO_WA_CONTENT_SID
        ? sendWhatsAppTemplate(waE164, TWILIO_WA_CONTENT_SID, { "1": vendorName || "", "2": "signup pending" })
        : sendWhatsApp(waE164, vendorText)
      )
      : null,
  ].filter(Boolean));
}

// ==============================
// Notifications — Proposals
// ==============================
async function notifyProposalSubmitted(p) {
  try {
    const id = p.proposal_id || p.proposalId;
    const adminLink = APP_BASE_URL ? `${APP_BASE_URL}/admin/proposals/${id}` : null;

    const subject = `📥 New proposal submitted`;
    const lines = [
      `📥 New proposal submitted`,
      `Org: ${p.org_name || ""}`,
      `Title: ${p.title || ""}`,
      `Budget: $${p.amount_usd ?? 0}`,
      adminLink ? `Admin: ${adminLink}` : "",
    ].filter(Boolean);
    const text = lines.join("\n");
    const html = lines.join("<br>");

    // proposer contacts
    const proposerEmails = [p.contact, p.owner_email].map(s => (s || "").trim()).filter(Boolean);
    const proposerPhone = toE164(p.owner_phone || "");
    const proposerTg = (p.owner_telegram_chat_id || "").trim();

    await Promise.all([
      // Admins
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,
      ...(ADMIN_WHATSAPP || []).map(n =>
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": p.title || "", "2": p.org_name || "" })
          : sendWhatsApp(n, text)
      ),

      // Proposer
      proposerTg ? sendTelegram([proposerTg], text) : null,
      proposerEmails.length ? sendEmail(proposerEmails, subject, html) : null,
      proposerPhone ? sendWhatsApp(proposerPhone, text) : null,
    ].filter(Boolean));
  } catch (e) {
    console.warn('notifyProposalSubmitted failed:', e);
  }
}

// ==============================
// Notifications — Proposal Rejected
// ==============================
async function notifyProposalRejected(p, reason) {
  try {
    const id = p.proposal_id || p.proposalId;
    const adminLink = APP_BASE_URL ? `${APP_BASE_URL}/admin/proposals/${id}` : null;

    const subject = `❌ Proposal rejected`;
    const lines = [
      `❌ Proposal rejected`,
      `Org: ${p.org_name || ""}`,
      `Title: ${p.title || ""}`,
      `Budget: $${p.amount_usd ?? 0}`,
      reason ? `Reason: ${reason}` : "",
      adminLink ? `Admin: ${adminLink}` : "",
    ].filter(Boolean);
    const text = lines.join("\n");
    const html = lines.join("<br>");

    // Proposer contacts
    const proposerEmails = [p.contact, p.owner_email].map(s => (s || "").trim()).filter(Boolean);
    const proposerPhone = toE164(p.owner_phone || "");
    const proposerTg = (p.owner_telegram_chat_id || "").trim();

    await Promise.all([
      // Admins
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,
      ...(ADMIN_WHATSAPP || []).map(n =>
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": p.title || "", "2": "rejected" })
          : sendWhatsApp(n, text)
      ),

      // Proposer
      proposerTg ? sendTelegram([proposerTg], text) : null,
      proposerEmails.length ? sendEmail(proposerEmails, subject, html) : null,
      proposerPhone ? sendWhatsApp(proposerPhone, text) : null,
    ].filter(Boolean));
  } catch (e) {
    console.warn('notifyProposalRejected failed:', e);
  }
}

// ==============================
// Notifications — Bids (EN/ES)
// ==============================
async function notifyBidApproved(bid, proposal, vendor) {
  try {
    const subject = `✅ Bid awarded`;
    const title = proposal?.title || "(untitled)";
    const org = proposal?.org_name || "";
    const vendorStr = bid?.vendor_name || vendor?.vendor_name || "";
    const amountStr = `$${bid?.price_usd ?? 0}`;
    const adminLink = APP_BASE_URL ? `${APP_BASE_URL}/admin/bids` : "";

    // Build bilingual body
    const en = [
      '✅ Bid awarded',
      `Project: ${title}${org ? ` (${org})` : ''}`,
      `Vendor: ${vendorStr}`,
      `Amount: ${amountStr}`,
      adminLink ? `Admin: ${adminLink}` : '',
    ].filter(Boolean).join('\n');

    const es = [
      '✅ Oferta adjudicada',
      `Proyecto: ${title}${org ? ` (${org})` : ''}`,
      `Proveedor: ${vendorStr}`,
      `Importe: ${amountStr}`,
      adminLink ? `Admin: ${adminLink}` : '',
    ].filter(Boolean).join('\n');

    const { text, html } = bi(en, es); // uses your existing helper

    // Vendor contacts
    const vendorEmails = [vendor?.email].map(s => (s || "").trim()).filter(Boolean);
    const vendorPhone = toE164(vendor?.phone || "");
    const vendorTg = (vendor?.telegram_chat_id || "").trim();

    await Promise.all([
      // Admins
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,
      ...(ADMIN_WHATSAPP || []).map(n =>
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": title, "2": "awarded" })
          : sendWhatsApp(n, text)
      ),

      // Vendor
      vendorTg ? sendTelegram([vendorTg], text) : null,
      vendorEmails.length ? sendEmail(vendorEmails, subject, html) : null,
      vendorPhone ? sendWhatsApp(vendorPhone, text) : null,
    ].filter(Boolean));
  } catch (e) {
    console.warn('notifyBidApproved failed:', e);
  }
}

async function notifyBidRejected(bid, proposal, vendor, reason) {
  try {
    const subject = `❌ Bid rejected`;
    const lines = [
      `❌ Bid rejected`,
      `Project: ${proposal?.title || "(untitled)"}`,
      `Vendor: ${bid?.vendor_name || vendor?.vendor_name || ""}`,
      `Amount: $${bid?.price_usd ?? 0}`,
      reason ? `Reason: ${reason}` : "",
      APP_BASE_URL ? `Admin: ${APP_BASE_URL}/admin/bids` : "",
    ].filter(Boolean);
    const text = lines.join("\n");
    const html = lines.join("<br>");

    const vendorEmails = [vendor?.email].map(s => (s || "").trim()).filter(Boolean);
    const vendorPhone = toE164(vendor?.phone || "");
    const vendorTg = (vendor?.telegram_chat_id || "").trim();

    await Promise.all([
      // Admins
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,
      ...(ADMIN_WHATSAPP || []).map(n =>
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": proposal?.title || "", "2": "rejected" })
          : sendWhatsApp(n, text)
      ),

      // Vendor
      vendorTg ? sendTelegram([vendorTg], text) : null,
      vendorEmails.length ? sendEmail(vendorEmails, subject, html) : null,
      vendorPhone ? sendWhatsApp(vendorPhone, text) : null,
    ].filter(Boolean));
  } catch (e) {
    console.warn('notifyBidRejected failed:', e);
  }
}

function shouldNotify(analysis) {
  try {
    const conf = Number(analysis?.confidence);
    const fit = String(analysis?.fit || "").toLowerCase();
    const gaps = Array.isArray(analysis?.gaps) ? analysis.gaps : [];
    const text = String(analysis?.summary || "");
    const kw = /(do not match|mismatch|inconsistent|wrong|duplicate|reused|fake|ai-generated)/i;
    return (
      !Number.isFinite(conf) ||
      conf < NOTIFY_CONF_THRESHOLD ||
      fit === "low" ||
      gaps.length > 0 ||
      kw.test(text)
    );
  } catch { return true; }
}

/* ==== Helper: build bilingual text/html (ONE COPY ONLY) ==== */
function bi(en, es) {
  const text = `${en.trim()}\n\n${es.trim()}`;
  const html = [
    `<div>${en.trim().replace(/\n/g, '<br>')}</div>`,
    '<hr>',
    `<div>${es.trim().replace(/\n/g, '<br>')}</div>`
  ].join('\n');
  return { text, html };
}

// ==============================
// Notifications — Payment pending approval
// ==============================
async function notifyPaymentPending({ bid, proposal, msIndex, amount, method = 'safe', txRef = null }) {
  try {
    const title = proposal?.title || 'Project';
    const vendorStr = `${bid.vendor_name || ''} (${bid.wallet_address || ''})`.trim();
    const amountStr = `$${Number(amount || 0).toFixed(2)} USD`;
    const adminLink = APP_BASE_URL ? `${APP_BASE_URL}/admin/bids/${bid.bid_id}` : null;
    const subject = method === 'safe'
      ? '🔐 Payment pending approval'
      : '🟨 Payment processing';

    const en = [
      subject,
      `Project: ${title} — ${proposal?.org_name || ''}`,
      `Vendor: ${vendorStr}`,
      `Milestone: #${msIndex}  •  Amount: ${amountStr}`,
      method === 'safe' ? 'Method: Safe multisig' : 'Method: Direct transfer',
      txRef ? `Safe Tx: ${txRef}` : '',
      adminLink ? `Admin: ${adminLink}` : ''
    ].filter(Boolean).join('\n');

    const es = [
      method === 'safe' ? '🔐 Pago pendiente de aprobación' : '🟨 Pago en proceso',
      `Proyecto: ${title} — ${proposal?.org_name || ''}`,
      `Proveedor: ${vendorStr}`,
      `Hito: #${msIndex}  •  Importe: ${amountStr}`,
      method === 'safe' ? 'Método: Safe multisig' : 'Método: Transferencia directa',
      txRef ? `Safe Tx: ${txRef}` : '',
      adminLink ? `Admin: ${adminLink}` : ''
    ].filter(Boolean).join('\n');

    const { text, html } = bi(en, es);

    await Promise.all([
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,
      ...(ADMIN_WHATSAPP || []).map(n =>
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": title, "2": "payment pending" })
          : sendWhatsApp(n, text)
      ),
    ].filter(Boolean));
  } catch (e) {
    console.warn('notifyPaymentPending failed:', e);
  }
}

// ==============================
// Notifications — Bid Submitted
// ==============================
async function notifyBidSubmitted(bid, proposal, vendor) {
  try {
    const subject = `📝 New bid submitted`;

    const en = [
      '📝 New bid submitted',
      `Project: ${proposal?.title || '(untitled)'} (${proposal?.org_name || ''})`,
      `Vendor: ${bid?.vendor_name || vendor?.vendor_name || ''}`,
      `Amount: $${bid?.price_usd ?? 0}  •  Days: ${bid?.days ?? '-'}`,
      APP_BASE_URL ? `Admin: ${APP_BASE_URL}/admin/bids` : ''
    ].filter(Boolean).join('\n');

    const es = [
      '📝 Nueva oferta enviada',
      `Proyecto: ${proposal?.title || '(sin título)'} (${proposal?.org_name || ''})`,
      `Proveedor: ${bid?.vendor_name || vendor?.vendor_name || ''}`,
      `Importe: $${bid?.price_usd ?? 0}  •  Días: ${bid?.days ?? '-'}`,
      APP_BASE_URL ? `Admin: ${APP_BASE_URL}/admin/bids` : ''
    ].filter(Boolean).join('\n');

    const { text, html } = bi(en, es);

    // Vendor contacts (confirmation back to submitter)
    const vendorEmails = [vendor?.email].map(s => (s || "").trim()).filter(Boolean);
    const vendorPhone = toE164(vendor?.phone || "");
    const vendorTg = (vendor?.telegram_chat_id || "").trim();

    await Promise.all([
      // Admins
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,
      ...(ADMIN_WHATSAPP || []).map(n =>
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": proposal?.title || "", "2": "new bid" })
          : sendWhatsApp(n, text)
      ),

      // Vendor (submission confirmation)
      vendorTg ? sendTelegram([vendorTg], text) : null,
      vendorEmails.length ? sendEmail(vendorEmails, subject, html) : null,
      vendorPhone ? sendWhatsApp(vendorPhone, text) : null,
    ].filter(Boolean));
  } catch (e) {
    console.warn('notifyBidSubmitted failed:', e);
  }
}

// ==================================
// Notifications — Proof needs review
// ==================================
async function notifyProofFlag({ proof, bid, proposal, analysis }) {
  const msIndex = Number(proof.milestone_index) + 1;
  const subject = `⚠️ Proof needs review — ${proposal?.title || "Project"} (Milestone ${msIndex})`;
  const adminLink = APP_BASE_URL ? `${APP_BASE_URL}/admin/bids/${bid.bid_id}?tab=proofs` : "";
  const short = (s, n = 300) => (s || "").slice(0, n);

  // Build bilingual payload (EN + ES)
  const en = [
    '⚠️ Proof needs review',
    `Project: ${proposal?.title || '(untitled)'} — ${proposal?.org_name || ''}`,
    `Vendor: ${bid.vendor_name || ''} (${bid.wallet_address || ''})`,
    `Milestone: #${msIndex}`,
    `Confidence: ${analysis?.confidence ?? 'n/a'}  •  Fit: ${analysis?.fit || 'n/a'}`,
    `Summary: ${short(analysis?.summary, 400)}`,
    adminLink ? `Admin: ${adminLink}` : ''
  ].filter(Boolean).join('\n');

  const es = [
    '⚠️ La prueba requiere revisión',
    `Proyecto: ${proposal?.title || '(sin título)'} — ${proposal?.org_name || ''}`,
    `Proveedor: ${bid.vendor_name || ''} (${bid.wallet_address || ''})`,
    `Hito: #${msIndex}`,
    `Confianza: ${analysis?.confidence ?? 'n/a'}  •  Ajuste: ${analysis?.fit || 'n/a'}`,
    `Resumen: ${short(analysis?.summary, 400)}`,
    adminLink ? `Admin: ${adminLink}` : ''
  ].filter(Boolean).join('\n');

  const { text, html } = bi(en, es);

  try {
    await Promise.all([
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,
      ...(ADMIN_WHATSAPP || []).map(n =>
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": proposal?.title || "", "2": "proof needs review" })
          : sendWhatsApp(n, text)
      ),
    ].filter(Boolean));
  } catch (e) {
    console.warn('notifyProofFlag failed:', String(e).slice(0, 200));
  }
}

// ==============================
// Notifications — Proof Approved (EN/ES)
// ==============================
async function notifyProofApproved({ proof, bid, proposal, msIndex }) {
  try {
    const subject = `✅ Proof approved — ${proposal?.title || "Project"} (Milestone ${msIndex})`;
    const adminLink = APP_BASE_URL ? `${APP_BASE_URL}/admin/bids/${bid.bid_id}?tab=proofs` : "";

    // Bilingual text
    const en = [
      '✅ Proof approved',
      `Project: ${proposal?.title || '(untitled)'} — ${proposal?.org_name || ''}`,
      `Vendor: ${bid.vendor_name || ''} (${bid.wallet_address || ''})`,
      `Milestone: #${msIndex}`,
      adminLink ? `Admin: ${adminLink}` : ''
    ].filter(Boolean).join('\n');

    const es = [
      '✅ Prueba aprobada',
      `Proyecto: ${proposal?.title || '(sin título)'} — ${proposal?.org_name || ''}`,
      `Proveedor: ${bid.vendor_name || ''} (${bid.wallet_address || ''})`,
      `Hito: #${msIndex}`,
      adminLink ? `Admin: ${adminLink}` : ''
    ].filter(Boolean).join('\n');

    const { text, html } = bi(en, es);

    // ---- Admin broadcast (Telegram / Email / WhatsApp) ----
    await Promise.all([
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,
      ...(ADMIN_WHATSAPP || []).map(n =>
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": proposal?.title || "", "2": "proof approved" })
          : sendWhatsApp(n, text)
      ),
    ].filter(Boolean));

    // ---- Vendor (best‑effort) ----
    const { rows: vprows } = await pool.query(
      `SELECT email, phone, telegram_chat_id
         FROM vendor_profiles
        WHERE lower(wallet_address)=lower($1)
        LIMIT 1`,
      [(bid.wallet_address || "").toLowerCase()]
    );
    const vp = vprows[0] || {};
    const vendorEmail = (vp.email || "").trim();
    const vendorPhone = toE164(vp.phone || "");
    const vendorTg = (vp.telegram_chat_id || "").trim();

    await Promise.all([
      vendorTg ? sendTelegram([vendorTg], text) : null,
      vendorEmail ? sendEmail([vendorEmail], subject, html) : null,
      vendorPhone ? (
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(vendorPhone, TWILIO_WA_CONTENT_SID, { "1": proposal?.title || "", "2": "proof approved" })
          : sendWhatsApp(vendorPhone, text)
      ) : null,
    ].filter(Boolean));

    console.log("[notify] proof approved sent", { bidId: bid.bid_id, msIndex });
  } catch (e) {
    console.warn("[notify] proof approved failed:", String(e).slice(0, 200));
  }
}

// ========================================
// Notifications — Payment released (EN/ES)
// ========================================
async function notifyPaymentReleased({ bid, proposal, msIndex, amount, txHash }) {
  const subject = `💸 Payment released — ${proposal?.title || "Project"} (Milestone ${msIndex})`;
  const adminLink = APP_BASE_URL ? `${APP_BASE_URL}/admin/bids/${bid.bid_id}` : "";
  const amountStr = typeof amount === 'number' ? `$${Number(amount).toLocaleString()}` : String(amount || '');

  const en = [
    '💸 Payment released',
    `Project: ${proposal?.title || '(untitled)'} — ${proposal?.org_name || ''}`,
    `Vendor: ${bid.vendor_name || ''} (${bid.wallet_address || ''})`,
    `Milestone: #${msIndex}  •  Amount: ${amountStr}`,
    txHash ? `Tx: ${txHash}` : '',
    adminLink ? `Admin: ${adminLink}` : ''
  ].filter(Boolean).join('\n');

  const es = [
    '💸 Pago liberado',
    `Proyecto: ${proposal?.title || '(sin título)'} — ${proposal?.org_name || ''}`,
    `Proveedor: ${bid.vendor_name || ''} (${bid.wallet_address || ''})`,
    `Hito: #${msIndex}  •  Importe: ${amountStr}`,
    txHash ? `Tx: ${txHash}` : '',
    adminLink ? `Admin: ${adminLink}` : ''
  ].filter(Boolean).join('\n');

  const { text, html } = bi(en, es);

  // Admins
  await Promise.all([
    TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
    MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,
    ...(ADMIN_WHATSAPP || []).map(n =>
      TWILIO_WA_CONTENT_SID
        ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": proposal?.title || "", "2": "payment released" })
        : sendWhatsApp(n, text)
    ),
  ].filter(Boolean));

  // Vendor
  const { rows: vprows } = await pool.query(
    `SELECT email, phone, telegram_chat_id FROM vendor_profiles WHERE lower(wallet_address)=lower($1) AND tenant_id=$2 LIMIT 1`,
    [(bid.wallet_address || "").toLowerCase(), bid.tenant_id]
  );
  const vp = vprows[0] || {};
  const vendorEmail = (vp.email || "").trim();
  const vendorPhone = toE164(vp.phone || "");
  const vendorTg = (vp.telegram_chat_id || "").trim();

  await Promise.all([
    vendorTg ? sendTelegram([vendorTg], text) : null,
    vendorEmail ? sendEmail([vendorEmail], subject, html) : null,
    vendorPhone ? (
      TWILIO_WA_CONTENT_SID
        ? sendWhatsAppTemplate(vendorPhone, TWILIO_WA_CONTENT_SID, { "1": proposal?.title || "", "2": "payment released" })
        : sendWhatsApp(vendorPhone, text)
    ) : null,
  ].filter(Boolean));
}

async function notifyIpfsMissing({ bid, proposal, cid, where, proofId = null, url = null }) {
  try {
    const subject = `🟥 IPFS content missing`;
    const title = proposal?.title || 'Project';
    const bidStr = `Bid ${bid?.bid_id ?? ''}`.trim();
    const whereStr = where || 'unknown';

    const en = [
      '🟥 IPFS content missing',
      `Project: ${title} — ${proposal?.org_name || ''}`,
      `${bidStr}`,
      `CID: ${cid}`,
      `Where: ${whereStr}${proofId ? ` (proof ${proofId})` : ''}`,
      url ? `URL: ${url}` : ''
    ].filter(Boolean).join('\n');

    const es = [
      '🟥 Contenido IPFS ausente',
      `Proyecto: ${title} — ${proposal?.org_name || ''}`,
      `${bidStr}`,
      `CID: ${cid}`,
      `Dónde: ${whereStr}${proofId ? ` (prueba ${proofId})` : ''}`,
      url ? `URL: ${url}` : ''
    ].filter(Boolean).join('\n');

    const { text, html } = bi(en, es);

    await Promise.all([
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,
      ...(ADMIN_WHATSAPP || []).map(n =>
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": title, "2": "ipfs missing" })
          : sendWhatsApp(n, text)
      ),
    ].filter(Boolean));
  } catch (e) {
    console.warn('notifyIpfsMissing failed:', String(e).slice(0, 200));
  }
}

// --- Image helpers for vision models ---
const IMAGE_EXT_RE = /\.(png|jpe?g|gif|webp|bmp|tiff|svg)(\?|$)/i;
function isImageFile(f) {
  if (!f) return false;
  const n = String(f.name || f.url || '').toLowerCase();
  const mt = String(f.mimetype || '').toLowerCase();
  return IMAGE_EXT_RE.test(n) || mt.startsWith('image/');
}

// Helpers to read proposal docs and pull BEFORE images
function parseDocsToArray(docsRaw) {
  if (Array.isArray(docsRaw)) return docsRaw;
  if (typeof docsRaw === 'string') {
    try { const arr = JSON.parse(docsRaw); return Array.isArray(arr) ? arr : []; }
    catch { return []; }
  }
  return [];
}
function collectProposalImages(proposal) {
  const docs = parseDocsToArray(proposal?.docs);
  const seen = new Set();
  const out = [];
  for (const d of docs) {
    if (d && d.url && isImageFile(d) && !seen.has(d.url)) {
      seen.add(d.url);
      out.push(d);
    }
  }
  return out;
}

// --- Confidence & Next-Checks helpers (global, top-level) ---
function clamp01(n) {
  const x = Number(n);
  return Number.isFinite(x) ? Math.max(0, Math.min(1, x)) : null;
}

/**
 * Try to recover a confidence value from streamed text.
 * Looks for:
 *   - JSON-like `confidence`: 0.73
 *   - "Confidence: 0.73" (or 73%)
 *   - "Confidence score [0–1]: 0.62"
 * Returns number in [0,1] or null if none found.
 */
function extractConfidenceFromText(fullText) {
  if (!fullText || typeof fullText !== 'string') return null;

  // 1) JSON-like key
  let m = fullText.match(/"confidence"\s*:\s*([0-9]*\.?[0-9]+)/i)
    || fullText.match(/'confidence'\s*:\s*([0-9]*\.?[0-9]+)/i);
  if (m) {
    const v = clamp01(parseFloat(m[1]));
    if (v !== null) return v;
  }

  // 2) "Confidence: 0.73" or "Confidence 73%"
  m = fullText.match(/confidence[^0-9%]{0,10}([0-9]+(?:\.[0-9]+)?)\s*%/i);
  if (m) {
    const pct = parseFloat(m[1]);
    const v = clamp01(pct / 100);
    if (v !== null) return v;
  }
  m = fullText.match(/confidence[^0-9]{0,10}([0-9]*\.?[0-9]+)/i);
  if (m) {
    const v = clamp01(parseFloat(m[1]));
    if (v !== null) return v;
  }

  // 3) Heuristic phrases (very rough fallback)
  const lowish = /\b(?:unsure|uncertain|low confidence|inconclusive|insufficient evidence)\b/i.test(fullText);
  if (lowish) return 0.25;

  return null;
}

/**
 * Build "Next checks" suggestions based on what we saw.
 * Pass booleans about context so we can tailor suggestions.
 */
function buildNextChecks({ hasAnyPdfText = false, imageCount = 0, ocrSeen = false } = {}) {
  const items = [];

  // Generic
  items.push('Ask vendor for original files (not screenshots) with metadata.');
  items.push('Request a short video or screen capture proving the same result.');

  // Images present
  if (imageCount > 0) {
    items.push('Provide 2–3 additional photos from different angles / lighting.');
    items.push('Include one wide shot that shows context (workspace, tools, environment).');
    items.push('Share an unedited image export (no compression) if possible.');
  }

  // PDFs used or missing
  if (hasAnyPdfText) {
    items.push('Upload the source document (editable, not just PDF) for spot-checking.');
  } else {
    items.push('Provide a PDF or text document with clear step-by-step evidence.');
  }

  // OCR/text presence
  if (!ocrSeen) {
    items.push('Include a close-up photo of any labels, serials, or on-screen outputs.');
  }

  // Keep list concise (unique + 5–7 items)
  const seen = new Set();
  const uniq = [];
  for (const it of items) {
    const k = it.toLowerCase();
    if (!seen.has(k)) { seen.add(k); uniq.push(it); }
    if (uniq.length >= 7) break;
  }
  return uniq;
}

/** Build a vision user content payload: first text, then image_url entries */
function buildVisionUserContent(text, files = []) {
  const content = [{ type: 'text', text }];
  for (const f of files) {
    if (f?.url && isImageFile(f)) {
      content.push({ type: 'image_url', image_url: { url: f.url } });
    }
  }
  return content;
}

/* ===========================
   Admin Vendors helpers (ADDED)
   - robust email detection
   - rich address builder (street + houseNo + city + postal + country)
   =========================== */
function toObj(val) {
  if (!val) return null;
  if (typeof val === 'object') return val;
  if (typeof val === 'string') {
    try { const j = JSON.parse(val); return j && typeof j === 'object' ? j : { text: val }; }
    catch { return { text: val }; }
  }
  return null;
}
function flatten(obj, prefix = '', acc = []) {
  if (!obj || typeof obj !== 'object') return acc;
  for (const [k, v] of Object.entries(obj)) {
    const p = prefix ? `${prefix}.${k}` : k;
    acc.push([p.toLowerCase(), v]);
    if (v && typeof v === 'object') flatten(v, p, acc);
  }
  return acc;
}
function normalizeProfile(profileRaw) {
  const out = {
    email: null, phone: null, website: null,
    address: { line1: null, city: null, state: null, postalCode: null, country: null },
    addressText: null, addressFormatted: null, addressDisplay: null
  };
  if (!profileRaw) return out;

  // Accept several possible containers for an address object
  const addrObj =
    toObj(profileRaw.address) ||
    toObj(profileRaw.address_json) ||
    toObj(profileRaw.location) ||
    toObj(profileRaw.addr) ||
    toObj(profileRaw.addressObj) ||
    null;

  // Flatten both the whole profile row and the parsed address object
  const flat = flatten(profileRaw).concat(flatten(addrObj, 'address'));
  const flatMap = new Map(flat.map(([p, v]) => [p, v]));
  const pick = (...keys) => {
    for (const k of keys) {
      const v = flatMap.get(k.toLowerCase());
      if (v !== undefined && v !== null && `${v}`.trim() !== '') {
        return typeof v === 'string' ? v.trim() : v;
      }
    }
    return null;
  };

  // -------- EMAIL (broad + deep) ----------
  const emailRe = /^[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}$/i;
  let email = pick(
    'email', 'email_address', 'emailaddress', 'primary_email',
    'contact.email', 'contact.email_address', 'contactEmail',
    'business_email', 'work_email', 'owner_email'
  );
  if (!email) {
    const arr = pick('emails', 'contact.emails');
    if (Array.isArray(arr)) {
      for (const e of arr) {
        let s = typeof e === 'string' ? e : (e && typeof e.value === 'string' ? e.value : null);
        if (s) { s = s.replace(/^mailto:/i, '').trim(); if (emailRe.test(s)) { email = s; break; } }
      }
    }
  }
  if (!email) {
    for (const v of flatMap.values()) {
      if (typeof v === 'string') {
        const s = v.replace(/^mailto:/i, '').trim();
        if (emailRe.test(s)) { email = s; break; }
      }
    }
  }

  // -------- PHONE / WEBSITE ----------
  const phone = pick('phone', 'phone_number', 'contact.phone', 'contact.phone_number', 'mobile', 'contact.mobile');
  const website = pick('website', 'url', 'site', 'homepage', 'contact.website', 'contact.url');

  // -------- ADDRESS PARTS (now with many more synonyms) ----------
  // direct line1
  let line1 = pick(
    'address1', 'addr1', 'line1', 'line_1', 'address_line1', 'address_line_1', 'addressline1', 'addr_line1',
    'address.address1', 'address.addr1', 'address.line1', 'address.line_1', 'address.address_line1', 'address.addressline1', 'address.addr_line1'
  );

  // street name variants
  const street = pick(
    'street', 'street1', 'streetname', 'street_name', 'streetName',
    'road', 'road_name', 'roadname', 'strasse', 'straße', 'str',
    'address.street', 'address.street1', 'address.streetname', 'address.street_name', 'address.streetName',
    'address.road', 'address.road_name', 'address.roadname', 'address.strasse', 'address.straße', 'address.str'
  );

  // house/number variants
  const houseNo = pick(
    'house_number', 'housenumber', 'houseNo', 'house_no', 'houseNumber', 'house_num', 'houseno',
    'nr', 'no', 'numero', 'num', 'hausnummer', 'hausnr', 'hnr',
    'address.house_number', 'address.housenumber', 'address.houseNo', 'address.house_no', 'address.houseNumber', 'address.house_num', 'address.houseno',
    'address.nr', 'address.no', 'address.numero', 'address.num', 'address.hausnummer', 'address.hausnr', 'address.hnr'
  );

  if (!line1 && (street || houseNo)) {
    line1 = [street, houseNo].filter(Boolean).join(' ').replace(/\s+/g, ' ').trim() || null;
  }

  // city / state / postal / country (synonyms)
  const city = pick('city', 'town', 'locality', 'address.city', 'address.town', 'address.locality');
  const state = pick('state', 'region', 'province', 'county', 'address.state', 'address.region', 'address.province', 'address.county');
  const postalCode = pick('postalcode', 'postal_code', 'postcode', 'zip', 'zip_code', 'address.postalcode', 'address.postal_code', 'address.postcode', 'address.zip', 'address.zip_code');
  const country = pick('country', 'country_code', 'address.country', 'address.country_code');

  // explicit free-text variants we keep as-is
  const explicitText =
    pick('address_text', 'addresstext', 'address.freeform', 'address.text') ||
    (typeof profileRaw.address === 'string' ? profileRaw.address.trim() : null);

  // --- Fallback: derive line1 from free-text if it *looks* like a street (contains a number) ---
  if (!line1 && explicitText) {
    const firstSeg = explicitText.split(',')[0].trim();
    if (/\d/.test(firstSeg) && firstSeg.length >= 4) {
      line1 = firstSeg;
    }
  }

  // Build formatted & display strings
  const parts = [];
  if (line1) parts.push(line1);
  const cityState = [city, state].filter(Boolean).join(', ');
  if (cityState) parts.push(cityState);
  if (postalCode) parts.push(postalCode);
  if (country) parts.push(country);
  const formatted = parts.join(', ') || null;

  // Prefer richer (has line1) or longer computed string; otherwise fall back to explicit text
  const display = (line1 || (formatted && (!explicitText || formatted.length > explicitText.length)))
    ? (formatted || explicitText || null)
    : (explicitText || null);

  out.email = email || null;
  out.phone = phone || null;
  out.website = website || null;

  out.address = {
    line1: line1 || null,
    city: city || null,
    state: state || null,
    postalCode: postalCode || null,
    country: country || null
  };
  out.addressText = explicitText || null;
  out.addressFormatted = formatted || null;
  out.addressDisplay = display || null;

  return out;
}

// ==============================
// PDF Extraction (debug-friendly with retries)
// ==============================
async function extractPdfInfoFromDoc(doc, jwt) {
  if (!doc?.url) return { used: false, reason: "no_file" };
  const name = doc.name || "";
  const isPdfName = /\.pdf($|\?)/i.test(name);
  try {
    const buf = await fetchAsBuffer(doc.url, jwt);
    const first5 = buf.slice(0, 5).toString(); // "%PDF-"
    const isPdf = first5 === "%PDF-" || isPdfName || (doc.mimetype || "").toLowerCase().includes("pdf");
    if (!isPdf) {
      return { used: false, reason: "not_pdf", bytes: buf.length, first5 };
    }
    let text = "";
    try {
      const parsed = await pdfParse(buf);
      text = (parsed.text || "").replace(/\s+/g, " ").trim();
    } catch (e) {
      return { used: false, reason: "pdf_parse_failed", bytes: buf.length, first5, error: String(e).slice(0, 200) };
    }
    if (!text) return { used: false, reason: "no_text_extracted", bytes: buf.length, first5 };
    const capped = text.slice(0, 15000);
    return { used: true, text: capped, snippet: capped.slice(0, 400), chars: capped.length, bytes: buf.length, first5 };
  } catch (e) {
    return { used: false, reason: "http_error", error: String(e).slice(0, 200) };
  }
}

async function waitForPdfInfoFromDoc(doc, { maxMs = 12000, stepMs = 1500 } = {}, jwt) {
  const start = Date.now();
  let last = await extractPdfInfoFromDoc(doc, jwt);
  if (!doc?.url || last.reason === "not_pdf" || last.reason === "no_file") return last;
  while (!last.used && Date.now() - start < maxMs) {
    if (!["http_error", "no_text_extracted", "pdf_parse_failed"].includes(last.reason || "")) break;
    await new Promise((r) => setTimeout(r, stepMs));
    last = await extractPdfInfoFromDoc(doc, jwt);
  }
  return last;
}

// ==============================
// Pinata / IPFS
// ==============================
const { Readable } = require('stream');
const pinataSDK = require('@pinata/sdk');

// Initialize SDK
const pinata = new pinataSDK(process.env.PINATA_API_KEY, process.env.PINATA_SECRET_API_KEY);

// Helper: Wait with jitter (randomness) to prevent synchronized retries
const delay = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

async function pinataUploadFile(file, tenantId = null) {
  let pKey = process.env.PINATA_API_KEY;
  let pSecret = process.env.PINATA_SECRET_API_KEY;
  let pJwt = process.env.PINATA_JWT; // Fallback env JWT

  if (tenantId) {
    // Try JWT first (preferred by frontend settings)
    const tJwt = await tenantService.getTenantConfig(tenantId, 'pinata_jwt');
    if (tJwt) {
      pJwt = tJwt;
      pKey = null; // Clear keys if using JWT
      pSecret = null;
    } else {
      // Try Legacy Keys
      const tKey = await tenantService.getTenantConfig(tenantId, 'PINATA_API_KEY');
      const tSecret = await tenantService.getTenantConfig(tenantId, 'PINATA_SECRET_API_KEY');
      if (tKey && tSecret) {
        pKey = tKey;
        pSecret = tSecret;
        pJwt = null;
      }
    }
  }

  console.log(`[Pinata] Uploading file ${file.name} for tenant ${tenantId || 'default'}`);
  console.log(`[Pinata] Auth Mode: ${pJwt ? 'JWT (Masked: ' + pJwt.slice(0, 10) + '...)' : (pKey ? 'API Key' : 'NONE')}`);

  if (!pKey && !pSecret && !pJwt) {
    throw new Error("Pinata not configured (No Keys or JWT)");
  }

  let localPinata;
  if (pJwt) {
    localPinata = new pinataSDK({ pinataJWTKey: pJwt });
  } else {
    localPinata = new pinataSDK(pKey, pSecret);
  }

  // Increase max retries to 5 to be very safe
  const maxRetries = 5;
  let attempt = 0;

  while (attempt < maxRetries) {
    try {
      // 1. Create fresh stream for this attempt
      const stream = Readable.from(file.data);
      stream.path = file.name;

      const options = {
        pinataMetadata: { name: file.name },
        pinataOptions: { cidVersion: 0 }
      };

      // 2. Try Upload
      const result = await localPinata.pinFileToIPFS(stream, options);

      // Use configured gateway or fallback
      let gateway = "https://gateway.pinata.cloud";
      if (tenantId) {
        const tGw = await tenantService.getTenantConfig(tenantId, 'pinata_gateway');
        if (tGw) gateway = tGw.replace(/\/+$/, '');
      } else if (process.env.PINATA_GATEWAY_DOMAIN) {
        gateway = `https://${process.env.PINATA_GATEWAY_DOMAIN}`;
      }

      return {
        cid: result.IpfsHash,
        url: `${gateway}/ipfs/${result.IpfsHash}`,
        name: file.name,
        size: result.PinSize,
        timestamp: result.Timestamp
      };

    } catch (err) {
      // 3. Check for Rate Limit errors
      const isRateLimit = err?.reason === 'RATE_LIMITED' ||
        (err?.details && String(err.details).includes('slow down'));

      if (isRateLimit && attempt < maxRetries - 1) {
        // EXPONENTIAL BACKOFF: 2s -> 4s -> 8s -> 16s
        // We add Math.random() * 1000 to prevent two uploads from retrying at the exact same millisecond
        const waitTime = Math.pow(2, attempt + 1) * 1000 + (Math.random() * 1000);

        console.warn(`[Pinata] Rate limited. Pausing for ${Math.round(waitTime)}ms... (Attempt ${attempt + 1}/${maxRetries})`);

        await delay(waitTime);
        attempt++;
      } else {
        // If it's not a rate limit (e.g. auth error) or we ran out of retries
        console.error("Pinata SDK Error:", err);
        throw new Error("Pinata upload failed: " + (err.details || err.message));
      }
    }
  }
}

// =====================================================================
// MISSING FUNCTION: pinataUploadJson
// Paste this immediately after the 'pinataUploadFile' function
// =====================================================================
async function pinataUploadJson(jsonData, tenantId = null) {
  let pKey = process.env.PINATA_API_KEY;
  let pSecret = process.env.PINATA_SECRET_API_KEY;

  if (tenantId) {
    const tKey = await tenantService.getTenantConfig(tenantId, 'PINATA_API_KEY');
    const tSecret = await tenantService.getTenantConfig(tenantId, 'PINATA_SECRET_API_KEY');
    if (tKey && tSecret) {
      pKey = tKey;
      pSecret = tSecret;
    }
  }

  if (!pKey || !pSecret) {
    throw new Error("Pinata not configured");
  }

  const localPinata = new pinataSDK(pKey, pSecret);

  // Safety: Ensure we have an object
  const body = (typeof jsonData === 'string') ? JSON.parse(jsonData) : jsonData;

  // Retry logic config
  const maxRetries = 5;
  let attempt = 0;

  while (attempt < maxRetries) {
    try {
      const options = {
        pinataMetadata: {
          name: body.name || `json_${Date.now()}`, // Fallback name
        },
        pinataOptions: {
          cidVersion: 0
        }
      };

      // Perform the upload
      const result = await localPinata.pinJSONToIPFS(body, options);

      return {
        cid: result.IpfsHash,
        url: `https://gateway.pinata.cloud/ipfs/${result.IpfsHash}`,
        timestamp: result.Timestamp
      };

    } catch (err) {
      // Check for Rate Limit errors (same logic as your file uploader)
      const isRateLimit = err?.reason === 'RATE_LIMITED' ||
        (err?.details && String(err.details).includes('slow down'));

      if (isRateLimit && attempt < maxRetries - 1) {
        // Exponential Backoff with Jitter
        const waitTime = Math.pow(2, attempt + 1) * 1000 + (Math.random() * 1000);

        console.warn(`[Pinata JSON] Rate limited. Pausing for ${Math.round(waitTime)}ms... (Attempt ${attempt + 1}/${maxRetries})`);

        await delay(waitTime); // Uses your existing delay() helper
        attempt++;
      } else {
        // Fatal error
        console.error("Pinata JSON Upload Error:", err);
        throw new Error("Pinata JSON upload failed: " + (err.details || err.message));
      }
    }
  }
}
// ==============================
// HTTP helpers
// ==============================
/** Generic HTTP(S) request returning { status, body } */
function sendRequest(method, urlStr, headers = {}, body = null) {
  const u = new URL(urlStr);
  const lib = u.protocol === "https:" ? https : http;
  const options = {
    method,
    hostname: u.hostname,
    port: u.port || (u.protocol === "https:" ? 443 : 80),
    path: u.pathname + u.search,
    headers,
  };
  return new Promise((resolve, reject) => {
    const req = lib.request(options, (res) => {
      let data = "";
      res.setEncoding("utf8");
      res.on("data", (c) => (data += c));
      res.on("end", () => resolve({ status: res.statusCode || 0, body: data }));
    });
    req.on("error", reject);
    if (body) {
      if (typeof body.pipe === "function") body.pipe(req);
      else { req.write(body); req.end(); }
    } else req.end();
  });
}

// If PINATA_PUBLIC_GATEWAY is a full URL (e.g. https://gateway.pinata.cloud/ipfs/),
// rewrite /ipfs/<cid>/... to that base. Otherwise treat it as a bare hostname.
function rewriteToGateway(u, base) {
  try {
    const m = String(u).match(/\/ipfs\/([^/]+)(\/.*)?$/i);
    if (!m) return u;
    const cid = m[1];
    const rest = m[2] || "";
    const b = base.replace(/\/+$/, "/");
    return b.startsWith("http")
      ? b + cid + rest
      : (new URL(u)).toString().replace((new URL(u)).hostname, b);
  } catch { return u; }
}

function toPublicGateway(u) {
  const pub = process.env.PINATA_PUBLIC_GATEWAY || "https://gateway.pinata.cloud/ipfs/";
  return rewriteToGateway(u, pub);
}

// --- IPFS liveness helpers ---------------------------------------------------
function extractCidFromUrl(u) {
  try {
    const m = String(u || '').match(/\/ipfs\/([^/?#]+)/i);
    return m ? m[1] : null;
  } catch { return null; }
}

async function headOk(u, headers = {}) {
  try {
    const url = new URL(u);
    const lib = url.protocol === 'https:' ? https : http;
    const opts = {
      method: 'HEAD',
      hostname: url.hostname,
      port: url.port || (url.protocol === 'https:' ? 443 : 80),
      path: url.pathname + url.search,
      headers,
      timeout: 8000,
    };
    return await new Promise((resolve) => {
      const req = lib.request(opts, (res) => resolve((res.statusCode || 0) < 400));
      req.on('timeout', () => { try { req.destroy(); } catch { } resolve(false); });
      req.on('error', () => resolve(false));
      req.end();
    });
  } catch { return false; }
}

async function checkCidAlive(cid, jwt) {
  if (!cid) return false;
  // 1) your configured gateway (supports mypinata auth)
  const baseHost = PINATA_GATEWAY.replace(/^https?:\/\//, '');
  const primary = `https://${baseHost}/ipfs/${cid}`;
  const headers = {};
  if (/\.mypinata\.cloud$/i.test(baseHost)) {
    if (jwt) headers['Authorization'] = `Bearer ${jwt}`;
    if (PINATA_GATEWAY_TOKEN) headers['x-pinata-gateway-token'] = PINATA_GATEWAY_TOKEN;
  }
  if (await headOk(primary, headers)) return true;

  // 2) public fallbacks (Added your Dedicated Gateway at the top)
  const fallbacks = [
    `https://sapphire-given-snake-741.mypinata.cloud/ipfs/${cid}`, // ⚡ Fastest
    `https://cf-ipfs.com/ipfs/${cid}`,                             // Fast public
    `${(PINATA_PUBLIC_GATEWAY || 'https://gateway.pinata.cloud/ipfs/').replace(/\/+$/, '/')}${cid}`,
    `https://ipfs.io/ipfs/${cid}`,
    `https://dweb.link/ipfs/${cid}`,
  ];
  for (const u of fallbacks) if (await headOk(u)) return true;
  return false;
}

/** Fetch a URL into a Buffer (supports mypinata.cloud auth + public fallbacks) */
/** Fetch a URL into a Buffer (supports mypinata.cloud auth + public fallbacks) */
async function fetchAsBuffer(urlStr, jwt, tenantId = null) {
  // 1. 🛡️ SANITIZE: Remove trailing dots/punctuation
  let orig = String(urlStr).trim().replace(/[.,;]+$/, "");

  // 2. ⚡ HIJACK: If URL is using the slow public gateway, force swap to your FAST Dedicated Gateway
  // This prevents waiting 15s for a timeout before trying the good link.
  if (orig.includes("gateway.pinata.cloud")) {
    let dedicated = "sapphire-given-snake-741.mypinata.cloud"; // Default fallback
    if (tenantId) {
      const tGw = await tenantService.getTenantConfig(tenantId, 'pinata_gateway');
      if (tGw) dedicated = tGw.replace(/^https?:\/\//, '').replace(/\/+$/, '');
    } else if (process.env.PINATA_GATEWAY_DOMAIN) {
      dedicated = process.env.PINATA_GATEWAY_DOMAIN;
    }
    orig = orig.replace("gateway.pinata.cloud", dedicated);
  }

  function tryOnce(u, headers = {}) {
    return new Promise((resolve, reject) => {
      const url = new URL(u);
      const lib = url.protocol === "https:" ? https : http;
      const options = {
        method: "GET",
        hostname: url.hostname,
        port: url.port || (url.protocol === "https:" ? 443 : 80),
        path: url.pathname + url.search,
        headers,
        timeout: 60000 // ⚡ Increased to 60s to prevent premature timeouts on large files
      };
      const req = lib.request(options, (res) => {
        const code = res.statusCode || 0;
        if (code >= 400) return reject(new Error(`HTTP ${code} fetching ${u}`));
        const chunks = [];
        let total = 0;
        const CAP = 25 * 1024 * 1024; // 25MB
        res.on("data", (d) => {
          total += d.length;
          if (total > CAP) {
            req.destroy(new Error("Response too large"));
            return;
          }
          chunks.push(d);
        });
        res.on("end", () => resolve(Buffer.concat(chunks)));
      });
      req.on("timeout", () => { req.destroy(new Error("Timeout")); });
      req.on("error", reject);
      req.end();
    });
  }

  // 3. Setup Auth for Dedicated Gateway (Now applies to 'orig' because we swapped the domain above)
  const isDedicated = /\.mypinata\.cloud$/i.test(new URL(orig).hostname);
  const headers = {};
  if (isDedicated) {
    if (jwt) headers["Authorization"] = `Bearer ${jwt}`;
    if (PINATA_GATEWAY_TOKEN) headers["x-pinata-gateway-token"] = PINATA_GATEWAY_TOKEN;
  }

  // 4. Try the FAST URL first
  try {
    return await tryOnce(orig, headers);
  } catch (e) {
    // 5. Fallback Candidates (If Sapphire fails, try these)
    const candidates = [
      rewriteToGateway(orig, "https://cf-ipfs.com/ipfs/"),             // Cloudflare (Fast Public)
      rewriteToGateway(orig, "https://ipfs.io/ipfs/"),                 // IPFS Main
      rewriteToGateway(orig, "https://dweb.link/ipfs/"),               // Dweb
      toPublicGateway(orig)                                            // Original Public Pinata (Slowest)
    ];

    let lastErr = e;
    for (const u of candidates) {
      // Don't retry the exact same URL we just failed on
      if (u === orig) continue;
      try {
        return await tryOnce(u);
      } catch (err) {
        lastErr = err;
      }
    }
    throw lastErr;
  }
}

/** Promise.race timeout helper */
function withTimeout(p, ms, onTimeout) {
  let t;
  const timeoutP = new Promise((resolve) => {
    t = setTimeout(() => resolve(typeof onTimeout === 'function' ? onTimeout() : onTimeout), ms);
  });
  return Promise.race([p, timeoutP]).finally(() => clearTimeout(t));
}

// ---- AUDIT write helper (single place) ----
async function writeAudit(bidId, req, changes) {
  try {
    const actorWallet = req.user?.sub || req.user?.address || null;
    const actorRole = req.user?.role || 'vendor';
    const { rows } = await pool.query(
      `INSERT INTO bid_audits (bid_id, actor_wallet, actor_role, changes)
       VALUES ($1,$2,$3,$4)
       RETURNING audit_id`,
      [Number(bidId), actorWallet, actorRole, changes]
    );
    if (typeof enrichAuditRow === 'function') {
      enrichAuditRow(pool, rows[0].audit_id, pinataUploadFile).catch(() => null); // adds ipfs_cid & leaf_hash
    }
  } catch (e) {
    console.warn('writeAudit failed (non-fatal):', String(e).slice(0, 200));
  }
}

// ==============================
// Media metadata (EXIF/GPS) from remote URLs
// ==============================
const MEDIA_EXT_RE = /\.(png|jpe?g|gif|webp|bmp|tiff?|heic|heif|mp4|mov|avi|m4v)(\?|$)/i;

function isMediaFile(f) {
  if (!f) return false;
  const n = String(f.name || f.url || "").toLowerCase();
  const mt = String(f.mimetype || "").toLowerCase();
  return MEDIA_EXT_RE.test(n) || mt.startsWith("image/") || mt.startsWith("video/");
}

/** Convert a file URL to a small metadata object (EXIF/GPS, hashes) */
async function extractFileMetaFromUrl(file) {
  try {
    if (!file?.url) return null;

    // Reuse your existing fetchAsBuffer helper
    const buf = await fetchAsBuffer(toPublicGateway(file.url));
    const sha256 = crypto.createHash("sha256").update(buf).digest("hex");

    // Write to temp for exiftool
    const bare = (file.name || file.url).split("?")[0];
    const ext = path.extname(bare) || "";
    const tmp = path.join(os.tmpdir(), `exif-${Date.now()}-${Math.random().toString(36).slice(2)}${ext}`);
    await fs.writeFile(tmp, buf);

    let tags = null;
    try {
      tags = await withTimeout(exiftool.read(tmp), 4000, () => null);
    } catch { tags = null; }

    try { await fs.unlink(tmp); } catch { }

    const size = buf.length;
    const exif = tags ? {
      make: tags.Make || null,
      model: tags.Model || null,
      software: tags.Software || tags.ProcessingSoftware || null,
      mimeType: tags.MIMEType || tags.MimeType || null,
      imageWidth: tags.ImageWidth || tags.SourceImageWidth || null,
      imageHeight: tags.ImageHeight || tags.SourceImageHeight || null,
      megapixels: tags.Megapixels || null,
      createDate: tags.DateTimeOriginal || tags.CreateDate || tags.MediaCreateDate || null,
      modifyDate: tags.ModifyDate || null,
      gpsLatitude: Number.isFinite(tags.GPSLatitude) ? Number(tags.GPSLatitude) : null,
      gpsLongitude: Number.isFinite(tags.GPSLongitude) ? Number(tags.GPSLongitude) : null,
      gpsAltitude: tags.GPSAltitude ?? null,
      orientation: tags.Orientation || null,
    } : null;

    const suspectEdits = /photoshop|lightroom|gimp|snapseed|facetune|luminar|picsart|canva|after effects|premiere/i
      .test(String(exif?.software || ""));

    return {
      url: file.url,
      name: file.name || null,
      mimetype: file.mimetype || null,
      size,
      hashSha256: sha256,
      exif,
      suspectEdits,
    };
  } catch {
    return {
      url: file?.url || null,
      name: file?.name || null,
      mimetype: file?.mimetype || null,
      size: null,
      hashSha256: null,
      exif: null,
      suspectEdits: false,
    };
  }
}

/** Summarize an array of metadata objects for LLM context */
function summarizeMeta(metaArr = []) {
  const lines = [];
  for (const m of metaArr.slice(0, 10)) {
    const parts = [];
    if (m.exif?.createDate) parts.push(String(m.exif.createDate));
    if (Number.isFinite(m.exif?.gpsLatitude) && Number.isFinite(m.exif?.gpsLongitude)) {
      parts.push(`GPS ${m.exif.gpsLatitude.toFixed(6)}, ${m.exif.gpsLongitude.toFixed(6)}`);
    } else {
      parts.push(`GPS none`);
    }
    const cam = [m.exif?.make, m.exif?.model].filter(Boolean).join(" ");
    if (cam) parts.push(cam);
    if (m.exif?.software) parts.push(`Software ${m.exif.software}`);
    if (m.suspectEdits) parts.push("⚠︎ edited");
    lines.push(`- ${m.name || "file"} — ${parts.join(" • ")}`);
  }
  return lines.join("\n") || "(no EXIF/metadata available)";
}

// ==============================
// Reverse Geocode (country / city label from GPS)
// Uses OpenCage if OPENCAGE_API_KEY is set; falls back to Nominatim
// ==============================
async function reverseGeocode(lat, lon) {
  if (!Number.isFinite(lat) || !Number.isFinite(lon)) return null;

  // 1) OpenCage (recommended: set OPENCAGE_API_KEY)
  const ocKey = (process.env.OPENCAGE_API_KEY || '').trim();
  if (ocKey) {
    try {
      const url = `https://api.opencagedata.com/geocode/v1/json?q=${encodeURIComponent(lat + ',' + lon)}&key=${ocKey}&no_annotations=1&language=en`;
      const { status, body } = await sendRequest("GET", url, { Accept: "application/json" });
      if (status >= 200 && status < 300) {
        const json = JSON.parse(body || "{}");
        const comp = json?.results?.[0]?.components || {};
        const label = json?.results?.[0]?.formatted || null;

        const city =
          comp.city || comp.town || comp.village || comp.hamlet || comp.municipality || comp.locality || null;
        const state = comp.state || comp.region || comp.province || null;
        const country = comp.country || null;
        const postcode = comp.postcode || null;

        return {
          provider: "opencage",
          label,
          country,
          state,
          county: comp.county || null,
          city,
          suburb: comp.suburb || comp.neighbourhood || null,
          postcode,
        };
      }
    } catch (_) { }
  }

  // 2) Nominatim fallback (requires a UA; be a good citizen)
  try {
    const ua = process.env.NOMINATIM_UA || "LithiumX/1.0 (admin@yourdomain.com)";
    const url = `https://nominatim.openstreetmap.org/reverse?format=jsonv2&lat=${encodeURIComponent(lat)}&lon=${encodeURIComponent(lon)}&zoom=14&addressdetails=1`;
    const { status, body } = await sendRequest(
      "GET",
      url,
      { Accept: "application/json", "User-Agent": ua },
      null
    );
    if (status >= 200 && status < 300) {
      const json = JSON.parse(body || "{}");
      const a = json?.address || {};

      const city =
        a.city || a.town || a.village || a.hamlet || a.municipality || a.locality || null;
      const state = a.state || a.region || a.province || null;
      const country = a.country || null;
      const postcode = a.postcode || null;

      // best-effort readable label
      const bits = [city, state, country].filter(Boolean);
      const label = bits.join(", ") || json?.display_name || null;

      return {
        provider: "nominatim",
        label,
        country,
        state,
        county: a.county || null,
        city,
        suburb: a.suburb || a.neighbourhood || null,
        postcode,
      };
    }
  } catch (_) { }

  return null;
}

// --- Safe public geo (city/state only; ~1 km rounding) ---
const _geoCache = new Map();
const roundCoord = (n, places = 2) =>
  Number.isFinite(+n) ? Number((+n).toFixed(places)) : null;

async function buildSafeGeoForProof(proofRow) {
  const lat = Number(proofRow.gps_lat ?? proofRow.gpsLat);
  const lon = Number(proofRow.gps_lon ?? proofRow.gpsLon);

  // ⬇️ ADD THESE GUARDS (reject NaN, out-of-range, and the (0,0) sentinel)
  const inRange = (v, lo, hi) => Number.isFinite(v) && v >= lo && v <= hi;
  if (!inRange(lat, -90, 90) || !inRange(lon, -180, 180) || (lat === 0 && lon === 0)) {
    return null;
  }

  const cacheKey = `${lat.toFixed(4)},${lon.toFixed(4)}`;
  let rg = _geoCache.get(cacheKey);
  if (!rg) {
    try { rg = await reverseGeocode(lat, lon); } catch { rg = null; }
    _geoCache.set(cacheKey, rg);
  }

  const city = rg?.city || null;
  const state = rg?.state || null;
  const country = rg?.country || null;
  const label = rg?.label || [city, state, country].filter(Boolean).join(", ") || null;

  return {
    label,
    city, state, country,
    approx: { lat: roundCoord(lat, 2), lon: roundCoord(lon, 2) } // ~1km rounding
  };
}

// ==============================
// Blockchain service
// ==============================
class BlockchainService {
  constructor() {
    this.provider = new ethers.providers.JsonRpcProvider(SEPOLIA_RPC_URL);
    if (PRIVATE_KEY) {
      const pk = PRIVATE_KEY.startsWith("0x") ? PRIVATE_KEY : `0x${PRIVATE_KEY}`;
      this.signer = new ethers.Wallet(pk, this.provider);
    } else {
      this.signer = null;
    }
  }

  async sendToken(tokenSymbol, toAddress, amount, tenantId) {
    let signer = this.signer;

    // Try to load tenant-specific key
    if (tenantId) {
      const tenantKey = await tenantService.getTenantConfig(tenantId, 'ETH_PRIVATE_KEY');
      if (tenantKey) {
        const pk = tenantKey.startsWith("0x") ? tenantKey : `0x${tenantKey}`;
        signer = new ethers.Wallet(pk, this.provider);
      }
    }

    if (!signer) throw new Error("Blockchain not configured");
    const token = TOKENS[tokenSymbol];
    const contract = new ethers.Contract(token.address, ERC20_ABI, signer);
    const decimals = await contract.decimals();
    const amt = ethers.utils.parseUnits(amount.toString(), decimals);

    const balance = await contract.balanceOf(signer.address);
    if (balance.lt(amt)) throw new Error("Insufficient balance");

    // --- CHANGED SECTION START ---
    // Send the transaction
    const tx = await contract.transfer(toAddress, amt);

    // CRITICAL FIX: Do NOT await tx.wait() here. 
    // Return the hash immediately so the database gets updated instantly.
    console.log(`[Blockchain] Sent ${amount} ${tokenSymbol} -> ${toAddress}. Hash: ${tx.hash}`);

    return { hash: tx.hash, amount, token: tokenSymbol };
    // --- CHANGED SECTION END ---
  }

  async getBalance(tokenSymbol, tenantId) {
    let signer = this.signer;

    // Try to load tenant-specific key & RPC
    if (tenantId) {
      const [tenantKey, tenantRpc] = await Promise.all([
        tenantService.getTenantConfig(tenantId, 'ETH_PRIVATE_KEY'),
        tenantService.getTenantConfig(tenantId, 'ETH_RPC_URL')
      ]);

      if (!tenantKey) {
        throw new Error("Tenant Direct Payment (ETH_PRIVATE_KEY) not configured");
      }

      let provider = this.provider;
      if (tenantRpc) {
        provider = new ethers.providers.JsonRpcProvider(tenantRpc);
      }

      const pk = tenantKey.startsWith("0x") ? tenantKey : `0x${tenantKey}`;
      signer = new ethers.Wallet(pk, provider);
    }

    if (!signer) return 0;
    const token = TOKENS[tokenSymbol];
    const contract = new ethers.Contract(token.address, ERC20_ABI, signer);
    const balance = await contract.balanceOf(signer.address);
    const decimals = await contract.decimals();
    return parseFloat(ethers.utils.formatUnits(balance, decimals));
  }
}

const blockchainService = new BlockchainService();

// ==============================
// Tenant Service (Multi-Tenancy)
// ==============================

function encrypt(text) {
  if (!text) return text;
  try {
    const iv = crypto.randomBytes(IV_LENGTH);
    const cipher = crypto.createCipheriv('aes-256-cbc', Buffer.from(ENCRYPTION_KEY), iv);
    let encrypted = cipher.update(text);
    encrypted = Buffer.concat([encrypted, cipher.final()]);
    return iv.toString('hex') + ':' + encrypted.toString('hex');
  } catch (e) {
    console.error('[Encryption] Failed to encrypt:', e);
    return text; // Fallback to plain text (or throw)
  }
}

function decrypt(text) {
  if (!text) return text;
  try {
    const textParts = text.split(':');
    if (textParts.length < 2) return text; // Not encrypted or invalid format
    const iv = Buffer.from(textParts.shift(), 'hex');
    const encryptedText = Buffer.from(textParts.join(':'), 'hex');
    const decipher = crypto.createDecipheriv('aes-256-cbc', Buffer.from(ENCRYPTION_KEY), iv);
    let decrypted = decipher.update(encryptedText);
    decrypted = Buffer.concat([decrypted, decipher.final()]);
    return decrypted.toString();
  } catch (e) {
    console.error('[Encryption] Failed to decrypt:', e);
    return text; // Return original if decryption fails
  }
}

class TenantService {
  constructor(pool) {
    this.pool = pool;
    this.configCache = new Map(); // tenantId:key -> value
    this.cacheTTL = 60 * 1000; // 1 minute
  }

  async getTenantConfig(tenantId, key) {
    if (!tenantId) return null;
    const cacheKey = `${tenantId}:${key}`;
    const cached = this.configCache.get(cacheKey);
    if (cached && Date.now() - cached.at < this.cacheTTL) return cached.value;

    try {
      const { rows } = await this.pool.query(
        `SELECT value, is_encrypted FROM tenant_configs WHERE tenant_id = $1 AND key = $2`,
        [tenantId, key]
      );
      if (rows[0]) {
        let val = rows[0].value;
        if (rows[0].is_encrypted) {
          val = decrypt(val);
        }
        this.configCache.set(cacheKey, { value: val, at: Date.now() });
        return val;
      }
    } catch (e) {
      console.warn(`[TenantService] Failed to fetch config ${key} for ${tenantId}`, e);
    }
    return null;
  }

  async setTenantConfig(tenantId, key, value, isEncrypted = false) {
    const finalValue = isEncrypted ? encrypt(value) : value;
    await this.pool.query(
      `INSERT INTO tenant_configs (tenant_id, key, value, is_encrypted, updated_at)
       VALUES ($1, $2, $3, $4, NOW())
       ON CONFLICT (tenant_id, key) DO UPDATE SET
         value = EXCLUDED.value,
         is_encrypted = EXCLUDED.is_encrypted,
         updated_at = NOW()`,
      [tenantId, key, finalValue, isEncrypted]
    );
    this.configCache.delete(`${tenantId}:${key}`);
  }

  async createTenant(name, slug) {
    const { rows } = await this.pool.query(
      `INSERT INTO tenants (name, slug) VALUES ($1, $2) RETURNING id, name, slug`,
      [name, slug]
    );
    return rows[0];
  }
}

const tenantService = new TenantService(pool);

// ==============================
// Tenant Middleware
// ==============================
async function resolveTenant(req, res, next) {
  const tenantIdHeader = req.get('X-Tenant-ID');

  // 1. Try Header
  if (tenantIdHeader) {
    // Basic UUID validation
    if (/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(tenantIdHeader)) {
      req.tenantId = tenantIdHeader;
      console.log('[Middleware] resolveTenant: Found X-Tenant-ID header:', req.tenantId);
    } else {
      console.log('[Middleware] resolveTenant: Invalid X-Tenant-ID header:', tenantIdHeader);
    }
  }

  // 2. Try Cookie (Fallback for initial loads or missing headers)
  if (!req.tenantId && req.cookies && req.cookies.lx_tenant_id) {
    const cookieTenant = req.cookies.lx_tenant_id;
    if (/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i.test(cookieTenant)) {
      req.tenantId = cookieTenant;
    }
  }

  // 2. Default to Global Tenant if not found
  if (!req.tenantId) {
    req.tenantId = '00000000-0000-0000-0000-000000000000';
  }

  next();
}

// ==============================
// Validation Schemas
// ==============================
const proposalSchema = Joi.object({
  orgName: Joi.string().required(),
  title: Joi.string().required(),
  summary: Joi.string().required(),
  contact: Joi.string().email().required(),
  address: Joi.string().allow(""),
  city: Joi.string().allow(""),
  country: Joi.string().allow(""),
  amountUSD: Joi.number().min(0).default(0),
  docs: Joi.array().default([]),
  cid: Joi.string().allow(""),
  ownerEmail: Joi.string().email().allow(""), // ✅ NEW (optional)
  ownerPhone: Joi.string().allow("").optional(),
}).unknown(true);

const proposalUpdateSchema = Joi.object({
  orgName: Joi.string().min(2).max(160),
  title: Joi.string().min(2).max(200),
  summary: Joi.string(),
  contact: Joi.string().email().allow(""),
  address: Joi.string().allow(""),
  city: Joi.string().allow(""),
  country: Joi.string().allow(""),
  amountUSD: Joi.number().min(0),
  docs: Joi.array(),
  ownerEmail: Joi.string().email().allow(""),
  ownerPhone: Joi.string().allow(""),
}).min(1);

// Reusable file item schema (accept both mimetype and contentType)
const fileItemSchema = Joi.object({
  cid: Joi.string().optional(),
  url: Joi.string().uri().required(),
  name: Joi.string().required(),
  size: Joi.number().optional(),
  mimetype: Joi.string().optional(),
  contentType: Joi.string().optional(),
});

const bidSchema = Joi.object({
  proposalId: Joi.number().integer().required(),
  vendorName: Joi.string().required(),
  priceUSD: Joi.number().required(),
  days: Joi.number().integer().required(),
  notes: Joi.string().allow(""),
  walletAddress: Joi.string().pattern(/^0x[a-fA-F0-9]{40}$/).required(),
  preferredStablecoin: Joi.string().valid("USDT", "USDC").default("USDT"),
  milestones: Joi.array().items(Joi.object({
    name: Joi.string().required(),
    amount: Joi.number().required(),
    dueDate: Joi.date().iso().required(),
  })).min(1).required(),

  // Back-compat single file (still supported)
  doc: fileItemSchema.optional().allow(null),

  // NEW: multi-file payload
  files: Joi.array().items(fileItemSchema).max(20).default([]),
});

// ==============================
// Agent2 helpers (prompt + normalization)
// ==============================
function buildAgent2Prompt({ bidRow, proposalRow, milestones, pdfInfo, promptOverride }) {
  const contextBlock = `
CONTEXT
-------
Proposal:
- Org: ${proposalRow?.org_name || ""}
- Title: ${proposalRow?.title || ""}
- Summary: ${proposalRow?.summary || ""}
- BudgetUSD: ${proposalRow?.amount_usd ?? 0}

Bid:
- Vendor: ${bidRow?.vendor_name || ""}
- PriceUSD: ${bidRow?.price_usd ?? 0}
- Days: ${bidRow?.days ?? 0}
- Notes: ${bidRow?.notes || ""}
- Milestones: ${JSON.stringify(milestones)}
`.trim();

  const pdfBlock = pdfInfo.used
    ? `PDF EXTRACT (truncated to ~15k chars):
"""${pdfInfo.text}"""`
    : `NO PDF TEXT AVAILABLE (reason: ${pdfInfo.reason || "unknown"})`;

  const mustInclude = pdfInfo.used
    ? `
REQUIREMENTS
------------
- In the "summary" string, include a subsection titled exactly: "PDF Insights".
- Quote 1–2 very short excerpts (<= 20 words each) from the PDF if possible.
- Explain how the PDF content affects feasibility, fit, risks, and milestones.`
    : `
REQUIREMENTS
------------
- In the "summary" string, explicitly state that no PDF text was available/usable and that the analysis did not use PDF contents.`;

  const outputSpec = `
Return JSON with exactly these keys:
{
  "summary": string,
  "risks": string[],
  "fit": "low" | "medium" | "high",
  "milestoneNotes": string[],
  "confidence": number
}`.trim();

  if (promptOverride && promptOverride.trim()) {
    const base = `${contextBlock}

${pdfBlock}

${mustInclude}

${outputSpec}`;
    return promptOverride.includes("{{CONTEXT}}")
      ? promptOverride.replace("{{CONTEXT}}", base)
      : `${base}

ADDITIONAL INSTRUCTIONS
----------------------
${promptOverride}`;
  }

  return `
You are Agent2. Analyze this vendor bid for a proposal and return strict JSON only.

${contextBlock}

${pdfBlock}

${mustInclude}

${outputSpec}
`.trim();
}

// Ensures Agent2 fields are safe to render
function normalizeAnalysisShape(core) {
  const safe = {};

  // summary
  if (typeof core?.summary === "string") {
    safe.summary = core.summary;
  } else if (core?.summary != null) {
    try { safe.summary = JSON.stringify(core.summary, null, 2); }
    catch { safe.summary = String(core.summary); }
  } else {
    safe.summary = "";
  }

  // risks -> array of strings
  safe.risks = Array.isArray(core?.risks) ? core.risks.map((r) => String(r)) : [];

  // fit -> one of low|medium|high
  const fit = String(core?.fit || "").toLowerCase();
  safe.fit = ["low", "medium", "high"].includes(fit) ? fit : "low";

  // milestoneNotes -> array of strings
  safe.milestoneNotes = Array.isArray(core?.milestoneNotes)
    ? core.milestoneNotes.map((m) => String(m))
    : [];

  // confidence -> clamp [0,1]
  const conf = Number(core?.confidence);
  safe.confidence = Number.isFinite(conf) ? Math.max(0, Math.min(1, conf)) : 0;

  return safe;
}

async function runAgent2OnBid(bidRow, proposalRow, { promptOverride, tenantId } = {}) {
  // 1. Resolve OpenAI Client (Tenant > Global)
  let localOpenai = openai; // Default global

  if (tenantId) {
    const tenantKey = await tenantService.getTenantConfig(tenantId, 'OPENAI_API_KEY');
    if (tenantKey) {
      localOpenai = new OpenAI({
        apiKey: tenantKey,
        project: process.env.OPENAI_PROJECT || undefined,
        organization: process.env.OPENAI_ORG || undefined,
      });
    }
  }

  if (!localOpenai) {
    return {
      status: "error",
      summary: "OpenAI is not configured.",
      risks: [],
      fit: "low",
      milestoneNotes: [],
      confidence: 0,
      pdfUsed: false,
      pdfChars: 0,
      pdfSnippet: null,
      promptSource: promptOverride ? "override" : "default",
      promptExcerpt: (promptOverride || "").slice(0, 300),
      pdfDebug: { reason: "openai_missing" },
    };
  }

  const milestones = Array.isArray(bidRow.milestones)
    ? bidRow.milestones
    : JSON.parse(bidRow.milestones || "[]");

  const docObj = coerceJson(bidRow.doc);
  let pdfInfo = { used: false, reason: "no_file" };
  try {
    const pinataJwt = tenantId ? await tenantService.getTenantConfig(tenantId, 'pinata_jwt') : null;
    pdfInfo = await waitForPdfInfoFromDoc(docObj, {}, pinataJwt);
  } catch (e) {
    pdfInfo = { used: false, reason: "extract_exception", error: String(e).slice(0, 200) };
  }

  const prompt = buildAgent2Prompt({
    bidRow,
    proposalRow,
    milestones,
    pdfInfo,
    promptOverride: typeof promptOverride === "string" ? promptOverride : ""
  });

  try {
    const resp = await localOpenai.chat.completions.create({
      model: "gpt-4o-mini",
      temperature: 0.2,
      messages: [{ role: "user", content: prompt }],
      response_format: { type: "json_object" },
    });

    const raw = resp.choices?.[0]?.message?.content || "{}";
    let core;
    try { core = JSON.parse(raw); } catch { core = {}; }

    const safeCore = normalizeAnalysisShape(core);

    return {
      status: "ready",
      ...safeCore,
      pdfUsed: !!pdfInfo.used,
      pdfChars: pdfInfo.chars || 0,
      pdfSnippet: pdfInfo.snippet || null,
      promptSource: promptOverride ? "override" : "default",
      promptExcerpt: prompt.slice(0, 300),
      pdfDebug: {
        url: docObj?.url || null,
        name: docObj?.name || null,
        reason: pdfInfo.reason || null,
        bytes: pdfInfo.bytes || null,
        first5: pdfInfo.first5 || null,
        error: pdfInfo.error || null,
      },
    };
  } catch (e) {
    return {
      status: "error",
      summary: "Agent2 failed to produce analysis.",
      risks: [],
      fit: "low",
      milestoneNotes: [],
      confidence: 0,
      pdfUsed: false,
      pdfChars: 0,
      pdfSnippet: null,
      promptSource: promptOverride ? "override" : "default",
      promptExcerpt: (promptOverride || "").slice(0, 300),
      pdfDebug: { reason: "agent2_error", error: String(e).slice(0, 200) },
    };
  }
}

// ==============================
// Express app
// ==============================
const app = express();
app.set("trust proxy", 1);

app.use(
  cors({
    origin: (origin, cb) => {
      if (!origin) return cb(null, true);
      if (CORS_ORIGINS.includes(origin)) return cb(null, true);
      return cb(new Error("Not allowed by CORS"));
    },
    credentials: true,
  })
);
app.use(helmet());
app.use(express.json({ limit: "20mb" }));
app.use(cookieParser()); // 🔐 parse JWT cookie
app.use(resolveTenant);    // 🏢 Multi-tenancy context

// Ensure JSON parsing is registered before admin routes
app.use(express.json({ limit: '2mb' }));

// DEBUG: Dump tenant members (Top Level)
app.get("/api/debug/tenant-members", async (req, res) => {
  try {
    const slug = req.query.slug;
    if (!slug) return res.json({ error: "no slug" });
    const { rows: tenant } = await pool.query("SELECT id FROM tenants WHERE slug=$1", [slug]);
    if (!tenant.length) return res.json({ error: "tenant not found" });

    const { rows: members } = await pool.query("SELECT * FROM tenant_members WHERE tenant_id=$1", [tenant[0].id]);
    res.json({ tenantId: tenant[0].id, members });
  } catch (e) { res.json({ error: e.message }); }
});

// DEBUG: Force Init DB (Run migrations manually)
app.get("/api/debug/init-db", async (req, res) => {
  try {
    // 3. Tenant Members (User Roles within a Tenant)
    await pool.query(`
      CREATE TABLE IF NOT EXISTS tenant_members (
        id SERIAL PRIMARY KEY,
        tenant_id UUID NOT NULL REFERENCES tenants(id) ON DELETE CASCADE,
        wallet_address TEXT NOT NULL,
        role TEXT NOT NULL, -- 'admin', 'vendor', 'proposer'
        created_at TIMESTAMPTZ DEFAULT NOW(),
        UNIQUE(tenant_id, wallet_address)
      );
    `);
    // 4. Add tenant_id to existing tables
    const tables = ['proposals', 'bids', 'proofs', 'vendor_profiles', 'proposer_profiles', 'school_reports', 'user_dashboard_state', 'milestone_payments'];
    for (const table of tables) {
      await pool.query(`
        ALTER TABLE ${table}
        ADD COLUMN IF NOT EXISTS tenant_id UUID REFERENCES tenants(id);
      `);
    }
    res.json({ ok: true, message: "DB init ran" });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// Debug: Check auth status for address/tenant
app.get('/api/debug/auth-check', async (req, res) => {
  try {
    const address = String(req.query.address || '').toLowerCase();
    const tenantId = req.query.tenantId;

    if (!address || !tenantId) return res.json({ error: 'Missing address or tenantId' });

    const { rows: members } = await pool.query(
      `SELECT * FROM tenant_members WHERE lower(wallet_address)=lower($1) AND tenant_id=$2`,
      [address, tenantId]
    );

    const roles = await durableRolesForAddress(address, tenantId);

    res.json({
      address,
      tenantId,
      members,
      durableRoles: roles
    });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// --- Accept both camelCase + snake_case + id/entityKey from clients
function normalizeEntitySelector(body = {}) {
  const norm = (v) => (v == null ? null : String(v).trim());

  return {
    // explicit triple
    entity: norm(body.entity ?? body.orgName ?? body.org_name),
    contactEmail: norm(body.contactEmail ?? body.ownerEmail ?? body.owner_email ?? body.contact ?? body.contact_email),
    wallet: norm(body.wallet ?? body.ownerWallet ?? body.owner_wallet ?? body.wallet_address),

    // fallback key used by /admin/proposers -> AdminEntitiesTable
    entityKey: norm(body.id ?? body.entityKey ?? body.entity_key),
  };
}

// ✅ This is the correct version. Use this for both.
async function buildEntityWhereAsync(pool, sel) {
  const cols = await detectProposalCols(pool);
  const clauses = [];
  const params = [];

  const eqGroup = (colsArr, idx) =>
    colsArr.map(c => `LOWER(TRIM(${c})) = LOWER(TRIM($${idx}))`).join(' OR ');

  const addEq = (value, colsArr) => {
    if (value && colsArr.length) {
      params.push(value);
      clauses.push(`(${eqGroup(colsArr, params.length)})`);
    }
  };

  // 1) explicit fields (any that are present)
  addEq(sel.wallet, cols.walletCols);
  addEq(sel.contactEmail, cols.emailCols);
  addEq(sel.entity, cols.orgCols);

  // 2) fallback: id/entityKey from /admin/proposers (match across any col)
  if (!clauses.length && sel.entityKey) {
    const all = [...cols.walletCols, ...cols.emailCols, ...cols.orgCols];
    if (all.length) {
      params.push(sel.entityKey);
      clauses.push(`(${eqGroup(all, params.length)})`);
    }
  }

  // If we have multiple clauses (wallet, email, entity), join with AND
  const whereSql = clauses.length ? clauses.join(' AND ') : ''; // <--- THIS IS THE FIX
  return { whereSql, params, cols };
}

// GET no-cache to make polling deterministic
app.use((req, res, next) => {
  if (req.method === 'GET') {
    res.set('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0');
    res.set('Pragma', 'no-cache');
  }
  next();
});

app.use(fileUpload({ limits: { fileSize: 50 * 1024 * 1024 } }));

// ==============================
// 🔐 Auth / Role (secure, non-breaking defaults)
// ==============================
const ADMIN_SET = new Set(
  (process.env.ADMIN_ADDRESSES || "")
    .split(",")
    .map((a) => a.trim().toLowerCase())
    .filter(Boolean)
);
const ADMIN_OVERRIDE_ADDR = norm(process.env.ADMIN_OVERRIDE_ADDR);
if (ADMIN_OVERRIDE_ADDR) ADMIN_SET.add(ADMIN_OVERRIDE_ADDR);
const JWT_SECRET = process.env.JWT_SECRET || "dev_fallback_secret_change_me";
const ENFORCE_JWT_ADMIN = String(process.env.ENFORCE_JWT_ADMIN || "false").toLowerCase() === "true";
const SCOPE_BIDS_FOR_VENDOR = String(process.env.SCOPE_BIDS_FOR_VENDOR || "false").toLowerCase() === "true";

const nonces = new Map(); // addressLower -> { nonce, exp }
function putNonce(address, nonce) {
  nonces.set(address, { nonce, exp: Date.now() + 5 * 60 * 1000 }); // 5 min
}
function getNonce(address) {
  const e = nonces.get(address);
  if (!e || e.exp < Date.now()) { nonces.delete(address); return null; }
  return e.nonce;
}

function norm(a) { return String(a || "").trim().toLowerCase(); }
function isAdminAddress(addr) { return ADMIN_SET.has(norm(addr)); }

function signJwt(payload, expiresIn = "7d") {
  return jwt.sign(payload, JWT_SECRET, { expiresIn });
}


// ==== AUTH GUARD (drop-in) ===============================================
// Place this block **right after** your verifyJwt() definition.

// ---- token helper (header first, then cookie)
function extractToken(req) {
  const h = req?.headers?.authorization || '';
  if (h.startsWith('Bearer ')) return h.slice(7);
  return req?.cookies?.auth_token || null;
}

function authGuard(req, res, next) {
  try {
    const token = extractToken(req);
    if (!token) return res.status(401).json({ error: 'unauthenticated' });

    const user = verifyJwt(token);
    if (!user?.sub) return res.status(401).json({ error: 'unauthenticated' });

    req.user = {
      address: String(user.sub).toLowerCase(),
      role: user.role || null,
      roles: Array.isArray(user.roles) ? user.roles : [],
      tenant_id: user.tenant_id || null
    };
    // Only set req.tenantId from JWT if not already set by resolveTenant (header)
    // OR if resolveTenant set the default '0000...' and JWT has a real one
    const isDefault = req.tenantId === '00000000-0000-0000-0000-000000000000';
    if ((!req.tenantId || isDefault) && user.tenant_id) {
      req.tenantId = user.tenant_id;
    }
    return next();
  } catch {
    return res.status(401).json({ error: 'unauthenticated' });
  }
}

// If some routes still use `requireAuth`, keep this alias:
const requireAuth = authGuard;

// ========================================================================

// Attach req.user if cookie is present (optional)
app.use((req, _res, next) => {
  const token = req.cookies?.auth_token;
  if (token) {
    const user = verifyJwt(token);
    if (user) req.user = user; // { sub: address, role }
  }
  next();
});

// 🔐 Also accept Authorization: Bearer <token>
app.use((req, _res, next) => {
  if (!req.user) {
    const auth = req.get("authorization") || "";
    const m = auth.match(/^bearer\s+(.+)$/i);
    if (m) {
      const user = verifyJwt(m[1]);
      if (user) req.user = user; // { sub, role }
    }
  }
  next();
});

function authRequired(req, res, next) {
  if (!req.user) return res.status(401).json({ error: "Unauthorized" });
  next();
}
function requireRole(role) {
  return (req, res, next) => {
    if (!req.user) return res.status(401).json({ error: "Unauthorized" });
    if (req.user.role !== role) return res.status(403).json({ error: "Forbidden" });
    next();
  };
}
// Admin guard that only enforces if ENFORCE_JWT_ADMIN=true
function adminGuard(req, res, next) {
  if (!ENFORCE_JWT_ADMIN) return next(); // compatibility mode
  if (!req.user) return res.status(401).json({ error: "Unauthorized" });

  // accept admin if current address is in ADMIN_SET (override), even if JWT role is stale
  const addr = norm(req.user.sub || req.user.address || req.user.walletAddress || "");
  const isAdminNow = isAdminAddress(addr);

  if (req.user.role !== "admin" && !isAdminNow) {
    console.log('[AdminGuard] 403 Forbidden. User:', req.user, 'Path:', req.path, 'IsAdminAddr:', isAdminNow);
    return res.status(403).json({
      error: "Forbidden",
      debug: {
        user: req.user,
        isAdminAddr: isAdminNow,
        tenantId: req.tenantId
      }
    });
  }
  next();
}

// ---- Cron auth helper (below adminGuard) ----
const MONITOR_SECRET = (process.env.MONITOR_SECRET || "").trim();

function allowCron(req, res, next) {
  // 1) Admin JWT ok
  const auth = req.get("authorization") || "";
  const m = auth.match(/^bearer\s+(.+)/i);
  if (m) {
    const user = verifyJwt(m[1]);
    if (user && (user.role === "admin" || isAdminAddress(user.sub))) {
      req.user = user;
      return next();
    }
  }

  // 2) Shared secret ok (query ?secret=... or header x-cron-secret)
  const sec = String(req.query.secret || req.get("x-cron-secret") || "").trim();
  if (MONITOR_SECRET && sec && sec === MONITOR_SECRET) return next();

  // 3) If admin enforcement is OFF, allow (same behavior as /admin/anchor)
  if (!ENFORCE_JWT_ADMIN) return next();

  return res.status(401).json({ error: "Unauthorized (need admin JWT or correct secret)" });
}

// Admin or bid owner guard (for /bids/:id/analyze/chat)
async function adminOrBidOwnerGuard(req, res, next) {
  if (req.user?.role === 'admin') return next();
  if (!req.user?.sub) return res.status(401).json({ error: 'Unauthorized' });

  const bidIdParam = (req.params.id ?? req.params.bidId);
  const bidId = Number(bidIdParam);
  if (!Number.isFinite(bidId)) return res.status(400).json({ error: 'Invalid bid id' });

  try {
    const { rows } = await pool.query('SELECT wallet_address FROM bids WHERE bid_id=$1', [bidId]);
    if (!rows[0]) return res.status(404).json({ error: 'Bid not found' });
    const owner = (rows[0].wallet_address || '').toLowerCase();
    if (owner !== (req.user.sub || '').toLowerCase()) {
      return res.status(403).json({ error: 'Forbidden' });
    }
    return next();
  } catch (e) {
    return res.status(500).json({ error: 'Internal error' });
  }
}

// --- Require approved vendor or admin ---
async function requireApprovedVendorOrAdmin(req, res, next) {
  try {
    if (!req.user) return res.status(401).json({ error: 'unauthorized' });

    // Admins always ok
    if (String(req.user.role || '').toLowerCase() === 'admin') return next();

    // Only vendors past this point
    if (String(req.user.role || '').toLowerCase() !== 'vendor') {
      return res.status(403).json({ error: 'forbidden_role' });
    }

    const addr = String(req.user.sub || '').toLowerCase();
    if (!addr) return res.status(401).json({ error: 'unauthorized' });

    const { rows } = await pool.query(
      `SELECT status FROM vendor_profiles WHERE lower(wallet_address)=lower($1) AND tenant_id=$2 LIMIT 1`,
      [addr, req.tenantId]
    );
    const status = (rows[0]?.status || 'pending').toLowerCase();
    if (status !== 'approved') {
      return res.status(403).json({ error: 'vendor_not_approved' });
    }

    return next();
  } catch (e) {
    console.error('requireApprovedVendorOrAdmin error', e);
    return res.status(500).json({ error: 'server_error' });
  }
}

async function adminOrProposalOwnerGuard(req, res, next) {
  if (req.user?.role === 'admin') return next();

  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: 'Invalid proposal id' });
  if (!req.user?.sub) return res.status(401).json({ error: 'Unauthorized' });

  try {
    const { rows } = await pool.query('SELECT owner_wallet FROM proposals WHERE proposal_id=$1', [id]);
    if (!rows[0]) return res.status(404).json({ error: 'Proposal not found' });
    const owner = (rows[0].owner_wallet || '').toLowerCase();
    if (owner !== (req.user.sub || '').toLowerCase()) {
      return res.status(403).json({ error: 'Forbidden' });
    }
    return next();
  } catch (e) {
    return res.status(500).json({ error: 'Internal error' });
  }
}

// --- Auth endpoints ---
app.post("/auth/nonce", (req, res) => {
  const address = norm(req.body?.address);
  if (!address) return res.status(400).json({ error: "address required" });
  const nonce = `LithiumX login nonce: ${Math.floor(Math.random() * 1e9)}`;
  putNonce(address, nonce);
  res.json({ nonce });
});

// REPLACE your existing /auth/verify with this:
app.post("/auth/verify", async (req, res) => {
  const address = norm(req.body?.address);
  const signature = req.body?.signature;
  const roleIntent = normalizeRoleIntent(req.body?.role || req.query?.role);

  if (!address || !signature) {
    return res.status(400).json({ error: "address and signature required" });
  }

  const nonce = getNonce(address);
  if (!nonce) {
    return res.status(400).json({ error: "nonce not found or expired" });
  }

  let recovered;
  try {
    recovered = ethers.utils.verifyMessage(nonce, signature);
  } catch {
    return res.status(400).json({ error: "invalid signature" });
  }

  if (norm(recovered) !== address) {
    return res.status(401).json({ error: "signature does not match address" });
  }

  // Determine durable roles and effective role (from intent)
  let roles = await durableRolesForAddress(address, req.tenantId);
  let role = roleFromDurableOrIntent(roles, roleIntent);
  if (!role) {
    return res.status(400).json({
      error: "role_required",
      message: 'Choose "vendor" (Submit a Bid) or "proposer" (Submit Proposal).'
    });
  }

  // Seed vendor profile ONLY when intent=vendor and the wallet isn't a vendor yet.
  if (role === "vendor" && !roles.includes("vendor")) {
    try {
      if (typeof __vendorSeedGuard === "number") __vendorSeedGuard++; // allow guarded insert here

      const w = (address || "").toLowerCase();
      const { rows } = await pool.query(
        `INSERT INTO vendor_profiles
           (wallet_address, vendor_name, email, phone, website, address, status, created_at, updated_at)
         VALUES ($1, '', NULL, NULL, NULL, NULL, 'pending', NOW(), NOW())
         ON CONFLICT (wallet_address) DO NOTHING
         RETURNING wallet_address, vendor_name, email, phone, telegram_chat_id, whatsapp`,
        [w]
      );

      // On first-ever insert → send notifications (best-effort)
      if (rows.length) {
        try {
          await Promise.allSettled([
            notifyVendorSignup?.({
              wallet: rows[0].wallet_address,
              vendorName: rows[0].vendor_name || "",
              email: rows[0].email || "",
              phone: rows[0].phone || ""
            }),
            notifyVendorSignupVendor?.({
              vendorName: rows[0].vendor_name || "",
              email: rows[0].email || "",
              phone: rows[0].phone || "",
              telegramChatId: rows[0].telegram_chat_id || null,
              whatsapp: rows[0].whatsapp || null
            })
          ]);
        } catch { }
      }
    } finally {
      if (typeof __vendorSeedGuard === "number") __vendorSeedGuard--;
    }

    // Refresh roles after possible insert
    roles = await durableRolesForAddress(address, req.tenantId);
  }

  // Admin override: admin wallets always act as admin
  if (isAdminAddress(address)) {
    roles = Array.from(new Set([...(roles || []), "admin"]));
    role = "admin";
  }

  const token = signJwt({ sub: address, role, roles });

  res.cookie("auth_token", token, {
    httpOnly: true,
    secure: true,
    sameSite: "none",
    maxAge: 7 * 24 * 3600 * 1000
  });

  // one-time nonce, then done
  nonces.delete(address);

  return res.json({ token, role, roles });
});

// nonce compat for frontend
app.get("/auth/nonce", (req, res) => {
  const address = norm(req.query.address);
  if (!address) return res.status(400).json({ error: "address required" });
  const nonce = `LithiumX login nonce: ${Math.floor(Math.random() * 1e9)}`;
  putNonce(address, nonce);
  res.json({ nonce });
});

// === Auth: login (nonce + signature -> JWT, role by intent; vendor seeding guarded) ===
app.post("/auth/login", async (req, res) => {
  const address = norm(req.body?.address);
  const signature = req.body?.signature;
  const roleIntent = normalizeRoleIntent(req.body?.role || req.query?.role);

  if (!address || !signature) {
    return res.status(400).json({ error: "address and signature required" });
  }

  const nonce = getNonce(address);
  if (!nonce) {
    return res.status(400).json({ error: "nonce not found or expired" });
  }

  let recovered;
  try {
    recovered = ethers.utils.verifyMessage(nonce, signature);
  } catch {
    return res.status(400).json({ error: "invalid signature" });
  }

  if (norm(recovered) !== address) {
    return res.status(401).json({ error: "signature does not match address" });
  }

  // Decide role from durable roles + button intent
  console.log('[Auth] Login request:', { address, roleIntent, tenantId: req.tenantId });
  let roles = await durableRolesForAddress(address, req.tenantId);
  console.log('[Auth] Durable roles found:', roles);
  let role = roleFromDurableOrIntent(roles, roleIntent);
  if (!role) {
    // 🛑 FIX: If login fails (e.g. trying to be admin on Root), check if they have tenants elsewhere
    try {
      const { rows: myTenants } = await pool.query(
        `SELECT t.slug, t.name, tm.role
         FROM tenant_members tm
         JOIN tenants t ON t.id = tm.tenant_id
         WHERE lower(tm.wallet_address) = lower($1)`,
        [address]
      );

      if (myTenants.length > 0) {
        // Return 200 with special action so frontend can redirect
        return res.json({
          action: 'select_tenant',
          tenants: myTenants
        });
      }
    } catch (e) {
      console.error('Error checking tenants:', e);
    }

    return res.status(400).json({
      error: "role_required",
      message: 'Choose "vendor" (Submit a Bid) or "proposer" (Submit Proposal).'
    });
  }

  // Seed vendor row ONLY when intent=vendor and user isn't a vendor yet AND isn't an admin
  if (role === "vendor" && !roles.includes("vendor") && !roles.includes("admin")) {
    __vendorSeedGuard++; // temporarily lift the global insert guard
    try {
      const w = address.toLowerCase();
      const { rows } = await pool.query(
        `INSERT INTO vendor_profiles
           (wallet_address, vendor_name, email, phone, website, address, status, created_at, updated_at, tenant_id)
         VALUES ($1, '', NULL, NULL, NULL, NULL, 'pending', NOW(), NOW(), $2)
         ON CONFLICT (wallet_address) DO NOTHING
         RETURNING wallet_address, vendor_name, email, phone, telegram_chat_id, whatsapp`,
        [w, req.tenantId]
      );

      if (rows && rows.length) {
        // first-time notifications (best-effort)
        try {
          await notifyVendorSignup({
            wallet: rows[0].wallet_address,
            vendorName: rows[0].vendor_name || "",
            email: rows[0].email || "",
            phone: rows[0].phone || ""
          });
        } catch { }
        try {
          await notifyVendorSignupVendor({
            vendorName: rows[0].vendor_name || "",
            email: rows[0].email || "",
            phone: rows[0].phone || "",
            telegramChatId: rows[0].telegram_chat_id || null,
            whatsapp: rows[0].whatsapp || null
          });
        } catch { }

        // reflect vendor in role set
        roles = Array.from(new Set([...(roles || []), "vendor"]));
      }
    } catch (e) {
      console.warn("vendor seed failed (non-fatal):", String(e).slice(0, 200));
    } finally {
      __vendorSeedGuard--; // restore guard
    }
  }

  // Admin override: force admin role if wallet is admin
  if (isAdminAddress(address)) {
    roles = Array.from(new Set([...(roles || []), "admin"]));
    role = "admin";
  }

  // Issue JWT + cookie
  const token = signJwt({ sub: address, role, roles });
  res.cookie("auth_token", token, {
    httpOnly: true,
    secure: true,
    sameSite: "none",
    maxAge: 7 * 24 * 3600 * 1000
  });

  // Single-use nonce
  nonces.delete(address);

  return res.json({ token, role, roles });
});

// ==== AUTH ROLE (cookie OR Bearer) ====
app.get('/auth/role', async (req, res) => {
  try {
    const token = readJwtFromReq(req);
    let payload = null, address = null;

    if (token) {
      payload = verifyJwt(token);
      address = String(payload?.sub || payload?.address || '').toLowerCase() || null;
    }

    // Compute durable roles even if only address is known
    let roles = [];
    if (address) {
      roles = await durableRolesForAddress(address, req.tenantId); // your existing function
      // ensure unique
      roles = Array.from(new Set(roles));
    }

    // Pick a primary role (admin > vendor/proposer > guest)
    let role = 'guest';
    if (roles.includes('admin')) role = 'admin';
    else if (roles.includes('vendor')) role = 'vendor';
    else if (roles.includes('proposer')) role = 'proposer';

    // vendorStatus for banner gating
    let vendorStatus = 'none';
    if (address) {
      const r = await pool.query(
        `SELECT status FROM vendor_profiles WHERE lower(wallet_address)=lower($1) LIMIT 1`,
        [address]
      );
      if (r.rows.length) vendorStatus = String(r.rows[0].status || 'pending');
    }

    // If payload had a role claim (from choose-role), prefer it when consistent
    const claimed = String(payload?.role || '').toLowerCase();
    if (claimed && (claimed === 'admin' || claimed === 'vendor' || claimed === 'proposer')) {
      // 🛑 FIX: Only respect the token's role if the user ACTUALLY HAS that role in this tenant
      if (roles.includes(claimed)) {
        role = claimed;
      }
    }

    return res.json({ address: address || null, role, roles, vendorStatus, tenantId: req.tenantId });
  } catch (e) {
    console.error('GET /auth/role error', e);
    return res.json({ address: null, role: 'guest', roles: [], vendorStatus: 'none' });
  }
});

app.post("/auth/switch-role", async (req, res) => {
  try {
    const token = req.headers.authorization?.startsWith('Bearer ')
      ? req.headers.authorization.slice(7)
      : req.cookies?.auth_token;

    if (!token) return res.status(401).json({ error: 'unauthenticated' });

    const user = verifyJwt(token);
    const address = String(user?.sub || '').trim();
    if (!address) return res.status(401).json({ error: 'unauthenticated' });

    const target = String(req.body?.role || '').toLowerCase();
    if (target !== 'vendor' && target !== 'proposer') {
      return res.status(400).json({ error: 'invalid_role' });
    }

    // Block: admins cannot switch to vendor unless explicitly allowed
    if (target === 'vendor' && isAdminAddress(address) && !req.body?.allowAdminVendor) {
      return res.status(403).json({ error: 'admin_cannot_be_vendor' });
    }

    const lower = address.toLowerCase();
    const roles = [];
    if (isAdminAddress(address)) roles.push('admin');

    // vendor role if vendor_profiles row exists
    const v = await pool.query(
      `SELECT 1 FROM vendor_profiles WHERE lower(wallet_address)=lower($1) AND tenant_id=$2 LIMIT 1`,
      [lower, req.tenantId]
    );
    if (v.rowCount > 0) roles.push('vendor');

    // ✅ proposer role if proposer_profiles row exists
    const pp = await pool.query(
      `SELECT 1 FROM proposer_profiles WHERE lower(wallet_address)=lower($1) AND tenant_id=$2 LIMIT 1`,
      [lower, req.tenantId]
    );
    if (pp.rowCount > 0) roles.push('proposer');

    // also proposer if they already own any proposals
    const p = await pool.query(
      `SELECT 1 FROM proposals WHERE lower(owner_wallet)=lower($1) AND tenant_id=$2 LIMIT 1`,
      [lower, req.tenantId]
    );
    if (p.rowCount > 0 && !roles.includes('proposer')) roles.push('proposer');

    // Issue a new token with preferred role + authoritative roles[]
    const newToken = signJwt({ sub: address, role: target, roles });
    res.cookie("auth_token", newToken, {
      httpOnly: true,
      secure: true,
      sameSite: "none",
      maxAge: 7 * 24 * 3600 * 1000,
    });

    // ✅ return token so client can store Bearer fallback
    return res.json({ role: target, roles, token: newToken });
  } catch (e) {
    console.error('/auth/switch-role error', e);
    return res.status(500).json({ error: 'server_error' });
  }
});


app.post("/auth/logout", (req, res) => {
  res.clearCookie("auth_token");
  res.json({ ok: true });
});

// ==============================
// Routes — Tenant Management
// ==============================

// Create a new tenant (Open for now, or restrict to super-admin)
app.post("/api/tenants", requireAuth, async (req, res) => {
  try {
    const { name, slug } = req.body;
    if (!name || !slug) return res.status(400).json({ error: "name and slug required" });

    const tenant = await tenantService.createTenant(name, slug);

    // Add creator as the first admin member
    // Add creator as the first admin member
    const creatorAddress = req.user?.address || req.user?.sub;
    console.log('[API] createTenant: Creator address:', creatorAddress, 'User obj:', req.user);

    let adminMember = null;
    if (creatorAddress) {
      try {
        await pool.query(
          `INSERT INTO tenant_members (tenant_id, wallet_address, role) VALUES ($1, $2, 'admin')`,
          [tenant.id, creatorAddress]
        );
        console.log('[API] createTenant: Added admin member:', creatorAddress, 'to tenant:', tenant.id);

        // Verify immediately
        const { rows: verify } = await pool.query(
          `SELECT * FROM tenant_members WHERE tenant_id=$1 AND wallet_address=$2`,
          [tenant.id, creatorAddress]
        );
        adminMember = verify[0];
        console.log('[API] createTenant: Verified admin member:', adminMember);
      } catch (err) {
        console.error('[API] createTenant: Failed to add admin member:', err);
      }
    } else {
      console.warn('[API] createTenant: No creator address found, skipping admin member add.');
    }

    res.json({ ...tenant, adminMember });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// Update Tenant Config (Admin only)
app.put("/api/tenants/:id/config", requireAuth, async (req, res) => {
  try {
    const { id } = req.params;
    const { key, value, isEncrypted } = req.body;

    // Authorization check: User must be an admin of this tenant
    const { rows: member } = await pool.query(
      `SELECT role FROM tenant_members WHERE tenant_id = $1 AND wallet_address = $2`,
      [id, req.user.sub]
    );

    if (!member[0] || member[0].role !== 'admin') {
      // Allow global admins to override
      if (!isAdminAddress(req.user.sub)) {
        return res.status(403).json({ error: "Forbidden" });
      }
    }

    await tenantService.setTenantConfig(id, key, value, isEncrypted);
    res.json({ ok: true });
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// Get Current Tenant Info
// Public lookup by slug (for frontend middleware)
app.get("/api/tenants/lookup", async (req, res) => {
  try {
    const slug = String(req.query.slug || "").trim();
    if (!slug) return res.status(400).json({ error: "Missing slug" });

    const { rows } = await pool.query(
      "SELECT id, name, slug FROM tenants WHERE lower(slug) = lower($1)",
      [slug]
    );
    if (!rows[0]) return res.status(404).json({ error: "Tenant not found" });

    res.json(rows[0]);
  } catch (e) {
    console.error("GET /api/tenants/lookup failed", e);
    res.status(500).json({ error: "Lookup failed" });
  }
});



app.get("/api/tenants/current", async (req, res) => {
  try {
    const { rows } = await pool.query(`SELECT id, name, slug FROM tenants WHERE id = $1`, [req.tenantId]);
    res.json(rows[0] || null);
  } catch (e) {
    res.status(500).json({ error: e.message });
  }
});

// Set Tenant Config (Admin Only)
app.post("/api/tenants/config", authGuard, adminGuard, async (req, res) => {
  try {
    const { key, value, isEncrypted } = req.body;
    if (!key || value === undefined) return res.status(400).json({ error: "key and value required" });

    // Allowlist of permitted keys to prevent abuse
    const ALLOWED_KEYS = ['pinata_jwt', 'pinata_gateway', 'payment_address', 'payment_stablecoin', 'safe_chain_id', 'safe_rpc_url', 'safe_owner_key', 'safe_service_url', 'safe_api_key', 'safe_reconcile_minutes', 'safe_threshold_usd', 'safe_address', 'ETH_PRIVATE_KEY', 'ETH_RPC_URL', 'ANCHOR_RPC_URL', 'ANCHOR_CHAIN_ID', 'ANCHOR_CONTRACT', 'ANCHOR_PRIVATE_KEY'];
    if (!ALLOWED_KEYS.includes(key)) {
      return res.status(400).json({ error: "Invalid config key" });
    }

    await tenantService.setTenantConfig(req.tenantId, key, value, !!isEncrypted);
    res.json({ ok: true });
  } catch (e) {
    console.error("POST /api/tenants/config failed", e);
    res.status(500).json({ error: e.message });
  }
});

// Get Tenant Config (Admin Only)
app.get("/api/tenants/config/:key", authGuard, adminGuard, async (req, res) => {
  try {
    const { key } = req.params;

    // Allowlist of permitted keys
    const ALLOWED_KEYS = ['pinata_jwt', 'pinata_gateway', 'payment_address', 'payment_stablecoin', 'safe_chain_id', 'safe_rpc_url', 'safe_owner_key', 'safe_service_url', 'safe_api_key', 'safe_reconcile_minutes', 'safe_threshold_usd', 'safe_address', 'ETH_PRIVATE_KEY', 'ETH_RPC_URL', 'ANCHOR_RPC_URL', 'ANCHOR_CHAIN_ID', 'ANCHOR_CONTRACT', 'ANCHOR_PRIVATE_KEY'];
    if (!ALLOWED_KEYS.includes(key)) {
      return res.status(400).json({ error: "Invalid config key" });
    }

    const val = await tenantService.getTenantConfig(req.tenantId, key);
    // Return wrapped object to handle nulls/empty strings clearly
    res.json({ value: val });
  } catch (e) {
    console.error("GET /api/tenants/config/:key failed", e);
    res.status(500).json({ error: e.message });
  }
});

// ==============================
// Routes — Health & Test
// ==============================
app.get("/health", async (_req, res) => {
  try {
    const { rows: proposals } = await pool.query("SELECT COUNT(*) FROM proposals");
    const { rows: bids } = await pool.query("SELECT COUNT(*) FROM bids");
    res.json({
      ok: true,
      proposals: Number(proposals[0].count || 0),
      bids: Number(bids[0].count || 0),
      blockchain: blockchainService.signer ? "configured" : "not_configured",
    });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});
app.get("/test", (_req, res) => res.json({ ok: true }));

// ==============================
// Routes — Proposals
// ==============================
// ==============================
// Routes — Proposals
// ==============================
app.get("/proposals", async (req, res) => {
  try {
    // 1. Determine if the caller is an admin
    const isAdmin = (req.user?.role === 'admin') || (req.user?.sub && isAdminAddress(req.user.sub));

    // 2. Parse query params
    const statusParam = (req.query.status || "").toLowerCase().trim();
    const includeArchived = String(req.query.includeArchived || "").toLowerCase();

    let q = "SELECT * FROM proposals";
    const params = [req.tenantId];
    const conditions = ["tenant_id = $1"];

    // 3. Apply Filtering Logic
    if (!isAdmin) {
      // 🔒 SECURITY: Non-admins (Public/Guests/Vendors) see ONLY approved proposals
      conditions.push("status = 'approved'");
    } else {
      // 🔓 ADMIN: Can filter by specific status, otherwise sees all non-archived
      if (statusParam) {
        params.push(statusParam);
        conditions.push(`status = $${params.length}`);
      } else if (!["true", "1", "yes"].includes(includeArchived)) {
        conditions.push("status != 'archived'");
      }
    }

    // 4. Construct Query
    if (conditions.length > 0) {
      q += " WHERE " + conditions.join(" AND ");
    }
    q += " ORDER BY created_at DESC";

    const { rows } = await pool.query(q, params);
    res.json(mapRows(rows));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});


/// ==============================
// Admin — “Entities” (proposers) helpers + routes  (REPLACE WHOLE SECTION)
// ==============================

// JSON body (must be before routes)
app.use(express.json({ limit: '2mb' }));

// ==== proposals column detector (deduped, hot-reload safe)
if (typeof globalThis.__lxProposalColsCache === 'undefined') {
  globalThis.__lxProposalColsCache = null;
}

async function detectProposalCols(pool) {
  if (globalThis.__lxProposalColsCache) return globalThis.__lxProposalColsCache;

  const { rows } = await pool.query(`
    SELECT LOWER(column_name) AS name
    FROM information_schema.columns
    WHERE table_name = 'proposals' AND table_schema = current_schema()
  `);

  const have = new Set(rows.map(r => r.name));
  const first = (cands) => cands.find(c => have.has(c)) || null;
  const present = (cands) => cands.filter(c => have.has(c));

  const orgCols = present(['org_name', 'org', 'organization', 'entity', 'orgname']);
  const emailCols = present(['contact', 'contact_email', 'owner_email', 'email', 'primary_email']);
  const walletCols = present(['owner_wallet', 'wallet', 'wallet_address', 'owner_wallet_address']);
  const statusCol = first(['status', 'proposal_status']);
  const updatedCol = first(['updated_at', 'updatedat', 'modified_at', 'modifiedat']);

  globalThis.__lxProposalColsCache = { orgCols, emailCols, walletCols, statusCol, updatedCol };
  return globalThis.__lxProposalColsCache;
}

// ---- Accept camelCase / snake_case / legacy keys
function normalizeEntitySelector(body = {}) {
  const norm = (v) => (v == null ? null : String(v).trim());
  return {
    // explicit triple
    entity: norm(body.entity ?? body.orgName ?? body.org_name),
    contactEmail: norm(body.contactEmail ?? body.ownerEmail ?? body.owner_email ?? body.contact ?? body.contact_email),
    wallet: norm(body.wallet ?? body.ownerWallet ?? body.owner_wallet ?? body.wallet_address),

    // fallback key used by some older UIs
    entityKey: norm(body.id ?? body.entityKey ?? body.entity_key),
  };
}

// ✅ This is the correct version. Use this for both.
async function buildEntityWhereAsync(pool, sel) {
  const cols = await detectProposalCols(pool);
  const clauses = [];
  const params = [];

  const eqGroup = (colsArr, idx) =>
    colsArr.map(c => `LOWER(TRIM(${c})) = LOWER(TRIM($${idx}))`).join(' OR ');

  const addEq = (value, colsArr) => {
    if (value && colsArr.length) {
      params.push(value);
      clauses.push(`(${eqGroup(colsArr, params.length)})`);
    }
  };

  // 1) explicit fields (any that are present)
  addEq(sel.wallet, cols.walletCols);
  addEq(sel.contactEmail, cols.emailCols);
  addEq(sel.entity, cols.orgCols);

  // 2) fallback: id/entityKey from /admin/proposers (match across any col)
  if (!clauses.length && sel.entityKey) {
    const all = [...cols.walletCols, ...cols.emailCols, ...cols.orgCols];
    if (all.length) {
      params.push(sel.entityKey);
      clauses.push(`(${eqGroup(all, params.length)})`);
    }
  }

  // If we have multiple clauses (wallet, email, entity), join with AND
  const whereSql = clauses.length ? clauses.join(' AND ') : ''; // <--- THIS IS THE FIX
  return { whereSql, params, cols };
}

// ==============================
// Actions — archive / unarchive / delete
// ==============================

// New helper function focused on identifying profiles
function buildWhereClauseForProfiles(sel) {
  const clauses = [];
  const params = [];

  const addClause = (val, col) => {
    // Only add a clause if the value is provided (truthy)
    if (val) {
      params.push(val);
      // Use LOWER(TRIM()) for case-insensitive, whitespace-tolerant matching
      clauses.push(`(LOWER(TRIM(${col})) = LOWER(TRIM($${params.length})))`);
    }
    // If val is not provided, we ignore this criteria.
  };

  // Build the WHERE clause based on the primary profile table columns
  addClause(sel.wallet, 'wallet_address');
  addClause(sel.contactEmail, 'contact_email');
  addClause(sel.entity, 'org_name');

  // Combine with AND to match based on all provided criteria
  return { whereClause: clauses.join(' AND '), params };
}

app.post('/admin/entities/archive', adminGuard, async (req, res) => {
  // 1. Get a dedicated client from the pool for the transaction
  const client = await pool.connect();

  try {
    const sel = normalizeEntitySelector(req.body || {});

    // --- Identify the target profiles ---
    const { whereClause, params } = buildWhereClauseForProfiles(sel);

    if (!whereClause) {
      return res.status(400).json({ error: 'Provide entity or contactEmail or wallet' });
    }

    // Find the wallet addresses (using the dedicated client)
    // Use client.query, NOT pool.query
    params.push(req.tenantId);
    const profileQuery = `
      SELECT wallet_address
      FROM proposer_profiles
      WHERE ${whereClause} AND status <> 'archived' AND tenant_id = $${params.length}
    `;

    const { rows } = await client.query(profileQuery, params);

    if (rows.length === 0) {
      return res.json({ ok: true, affected: 0 });
    }

    const walletAddresses = rows.map(row => row.wallet_address).filter(Boolean);

    if (walletAddresses.length === 0) {
      console.warn("Matching profiles found, but no wallet addresses associated.", sel);
      return res.json({ ok: true, affected: 0 });
    }

    // 2. START THE TRANSACTION
    await client.query('BEGIN');

    // 3. Archive 'proposer_profiles' (using the client)
    const { rowCount: rc1 } = await client.query(
      `UPDATE proposer_profiles
       SET status='archived', updated_at=NOW()
       WHERE wallet_address = ANY($1) AND status <> 'archived' AND tenant_id = $2`,
      [walletAddresses, req.tenantId]
    );

    // 4. Archive associated 'proposals' (using the client)
    const cols = await detectProposalCols(pool);
    if (!cols.statusCol) {
      // We MUST roll back before throwing or returning
      await client.query('ROLLBACK');
      return res.status(500).json({ error: 'proposals.status column not found' });
    }

    const setSql = cols.updatedCol
      ? `${cols.statusCol}='archived', ${cols.updatedCol}=NOW()`
      : `${cols.statusCol}='archived'`;

    const { rowCount: rc2 } = await client.query(
      `UPDATE proposals
       SET ${setSql}
       WHERE owner_wallet = ANY($1) AND ${cols.statusCol} <> 'archived' AND tenant_id = $2`,
      [walletAddresses, req.tenantId]
    );

    // 5. COMMIT THE TRANSACTION
    // This makes the changes permanent
    await client.query('COMMIT');

    return res.json({ ok: true, affected: (rc1 + rc2) });

  } catch (e) {
    // 6. ROLL BACK ON ANY ERROR
    // If anything failed, undo all changes from this transaction
    await client.query('ROLLBACK');

    console.error('archive entity error', e);
    return res.status(500).json({ error: 'Failed to archive entity' });

  } finally {
    // 7. ALWAYS RELEASE THE CLIENT
    // This returns the client to the pool, whether we committed or rolled back.
    client.release();
  }
});

app.post('/admin/entities/unarchive', adminGuard, async (req, res) => {
  // 1. Get a dedicated client from the pool
  const client = await pool.connect();

  try {
    const sel = normalizeEntitySelector(req.body || {});

    // --- Identify the target profiles (that are currently archived) ---
    const { whereClause, params } = buildWhereClauseForProfiles(sel);

    if (!whereClause) {
      return res.status(400).json({ error: 'Provide entity or contactEmail or wallet' });
    }

    // Find the wallet addresses (using the dedicated client)
    // Use client.query, NOT pool.query
    params.push(req.tenantId);
    const profileQuery = `
      SELECT wallet_address
      FROM proposer_profiles
      WHERE ${whereClause} AND status = 'archived' AND tenant_id = $${params.length}
    `;

    const { rows } = await client.query(profileQuery, params);

    if (rows.length === 0) {
      return res.json({ ok: true, affected: 0 });
    }

    const walletAddresses = rows.map(row => row.wallet_address).filter(Boolean);

    if (walletAddresses.length === 0) {
      console.warn("Matching archived profiles found, but no wallet addresses associated.", sel);
      return res.json({ ok: true, affected: 0 });
    }

    // 2. START THE TRANSACTION
    await client.query('BEGIN');

    // 3. Unarchive 'proposer_profiles' (set to 'active')
    const { rowCount: rc1 } = await client.query(
      `UPDATE proposer_profiles
       SET status='active', updated_at=NOW()
       WHERE wallet_address = ANY($1) AND status = 'archived' AND tenant_id = $2`,
      [walletAddresses, req.tenantId]
    );

    // 4. Unarchive associated 'proposals'
    const toStatusRaw = String(req.body?.toStatus || 'pending').toLowerCase();
    const toStatus = ['pending', 'approved', 'rejected'].includes(toStatusRaw) ? toStatusRaw : 'pending';

    const cols = await detectProposalCols(pool);
    if (!cols.statusCol) {
      // We MUST roll back
      await client.query('ROLLBACK');
      return res.status(500).json({ error: 'proposals.status column not found' });
    }

    const setSql = cols.updatedCol
      ? `${cols.statusCol}=$2, ${cols.updatedCol}=NOW()`
      : `${cols.statusCol}=$2`;

    const { rowCount: rc2 } = await client.query(
      `UPDATE proposals
       SET ${setSql}
       WHERE owner_wallet = ANY($1) AND ${cols.statusCol}='archived' AND tenant_id = $3`,
      [walletAddresses, toStatus, req.tenantId] // Pass both parameters
    );

    // 5. COMMIT THE TRANSACTION
    await client.query('COMMIT');

    return res.json({ ok: true, affected: (rc1 + rc2), toStatus });

  } catch (e) {
    // 6. ROLL BACK ON ANY ERROR
    await client.query('ROLLBACK');

    console.error('unarchive entity error', e);
    return res.status(500).json({ error: 'Failed to unarchive entity' });
  } finally {
    // 7. ALWAYS RELEASE THE CLIENT
    client.release();
  }
});

app.delete('/admin/entities', adminGuard, async (req, res) => {
  try {
    // This normalizeSelector function is correct and robust
    const sel = normalizeEntitySelector(req.body || {});

    // We must build WHERE clauses for BOTH tables, as their columns differ.
    const clauses_proposals = [];
    const clauses_proposer_profiles = [];
    const params = [];

    // This logic uses the 'sel' object to build params
    if (sel.wallet) {
      params.push(sel.wallet);
      // proposals table has owner_wallet
      clauses_proposals.push(`(LOWER(TRIM(owner_wallet)) = LOWER(TRIM($${params.length})))`);
      // proposer_profiles table has wallet_address
      clauses_proposer_profiles.push(`(LOWER(TRIM(wallet_address)) = LOWER(TRIM($${params.length})))`);
    }
    if (sel.contactEmail) {
      params.push(sel.contactEmail);
      // proposals table has contact
      clauses_proposals.push(`(LOWER(TRIM(contact)) = LOWER(TRIM($${params.length})))`);
      // proposer_profiles table has contact_email
      clauses_proposer_profiles.push(`(LOWER(TRIM(contact_email)) = LOWER(TRIM($${params.length})))`);
    }
    if (sel.entity) {
      params.push(sel.entity);
      // proposals table has org_name
      clauses_proposals.push(`(LOWER(TRIM(org_name)) = LOWER(TRIM($${params.length})))`);
      // proposer_profiles table has org_name
      clauses_proposer_profiles.push(`(LOWER(TRIM(org_name)) = LOWER(TRIM($${params.length})))`);
    }

    // Must have at least one valid parameter to build a query
    if (clauses_proposals.length === 0) {
      return res.status(400).json({ error: 'Provide entity or contactEmail or wallet' });
    }

    // Join with AND (this fixes the other bug from buildEntityWhereAsync)
    const where_proposals = clauses_proposals.join(' AND ');
    const where_proposer_profiles = clauses_proposer_profiles.join(' AND ');

    const mode = String(req.query.mode || 'soft').toLowerCase();

    if (mode === 'hard') {
      // ✅ SOLUTION: DELETE FROM BOTH TABLES
      params.push(req.tenantId);
      const tenantIdIdx = params.length;
      const { rowCount: rc1 } = await pool.query(`DELETE FROM proposals WHERE ${where_proposals} AND tenant_id=$${tenantIdIdx}`, params);
      const { rowCount: rc2 } = await pool.query(`DELETE FROM proposer_profiles WHERE ${where_proposer_profiles} AND tenant_id=$${tenantIdIdx}`, params);

      return res.json({ success: true, deleted: (rc1 + rc2), mode: 'hard' });
    }

    // --- SOFT DELETE (Archive) ---

    // 1. Soft delete on 'proposals'
    const { cols } = await detectProposalCols(pool); //
    if (!cols.statusCol) return res.status(500).json({ error: 'proposals.status column not found' });

    const setSql_proposals = cols.updatedCol
      ? `${cols.statusCol}='archived', ${cols.updatedCol}=NOW()`
      : `${cols.statusCol}='archived'`;

    params.push(req.tenantId);
    const tenantIdIdx = params.length;

    const { rowCount: rc1 } = await pool.query(
      `UPDATE proposals SET ${setSql_proposals} WHERE ${where_proposals} AND ${cols.statusCol} <> 'archived' AND tenant_id=$${tenantIdIdx}`,
      params
    );

    // 2. ✅ SOLUTION: Soft delete on 'proposer_profiles'
    const { rowCount: rc2 } = await pool.query(
      `UPDATE proposer_profiles SET status='archived', updated_at=NOW() WHERE ${where_proposer_profiles} AND status <> 'archived' AND tenant_id=$${tenantIdIdx}`,
      params
    );

    return res.json({ success: true, archived: (rc1 + rc2), mode: 'soft' });

  } catch (e) {
    console.error('delete entity error', e);
    return res.status(500).json({ error: 'Failed to delete entity' });
  }
});

// List proposals owned by the current user
app.get("/proposals/mine", authRequired, async (req, res) => {
  try {
    const includeArchived = String(req.query.includeArchived || "").toLowerCase();
    const wallet = String(req.user?.sub || "").toLowerCase();
    if (!wallet) return res.status(401).json({ error: "Unauthorized" });

    let q = `
      SELECT * FROM proposals
      WHERE lower(owner_wallet) = lower($1) AND tenant_id = $2
    `;
    const params = [wallet, req.tenantId];

    if (!["true", "1", "yes"].includes(includeArchived)) {
      q += ` AND status != 'archived'`;
    }

    q += ` ORDER BY created_at DESC`;

    const { rows } = await pool.query(q, params);
    res.json(mapRows(rows));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get("/proposals/:id", async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid id" });
    const { rows } = await pool.query("SELECT * FROM proposals WHERE proposal_id=$1 AND tenant_id=$2", [id, req.tenantId]);
    if (!rows[0]) return res.status(404).json({ error: "not found" });
    res.json(toCamel(rows[0]));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

const _nonEmpty = (s) => typeof s === 'string' && s.trim() !== '';

app.post("/proposals", authGuard /* or requireAuth */, async (req, res) => {
  try {
    const { error, value } = proposalSchema.validate(req.body);
    if (error) return res.status(400).json({ error: error.message });

    const ownerWallet = String(req.user?.address || req.user?.sub || "").toLowerCase();
    const ownerEmail = value.ownerEmail || null;
    const ownerPhone = toE164(value.ownerPhone || "");

    if (!ownerWallet) return res.status(401).json({ error: "Login required" });

    // ✅ ONLY ENTITY (proposer_profiles) may submit proposals.
    const { rows: ok } = await pool.query(
      `
      SELECT 1
        FROM proposer_profiles
       WHERE lower(wallet_address) = lower($1)
         AND tenant_id = $2
         AND (
           COALESCE(contact_email,'') <> ''
        OR COALESCE(phone,'') <> ''
        OR COALESCE(telegram_chat_id,'') <> ''
        OR COALESCE(telegram_username,'') <> ''
         )
       LIMIT 1
      `,
      [ownerWallet, req.tenantId]
    );

    if (!ok[0]) {
      return res.status(400).json({
        error: "Please complete your profile (add email, phone/WhatsApp, or Telegram) before submitting a proposal."
      });
    }

    // [FIXED] Added 'location' column to INSERT and RETURNING
    const q = `
      INSERT INTO proposals (
        org_name, title, summary, contact, address, city, country, amount_usd, docs, cid, status,
        owner_wallet, owner_email, owner_phone, location, tenant_id, updated_at
      ) VALUES (
        $1,$2,$3,$4,$5,$6,$7,$8,$9,$10,'pending',
        $11,$12,$13, $14, $15, NOW()
      )
      RETURNING proposal_id, org_name, title, summary, contact, address, city, country,
                amount_usd, docs, cid, status, created_at, owner_wallet, owner_email, owner_phone, location, tenant_id, updated_at
    `;

    // [FIXED] Added value.location to vals array (index 13 -> $14)
    const vals = [
      value.orgName,
      value.title,
      value.summary,
      value.contact,
      value.address,
      value.city,
      value.country,
      value.amountUSD,
      JSON.stringify(value.docs || []),
      value.cid ?? null,
      ownerWallet,
      ownerEmail,
      ownerPhone || null,
      value.location ? JSON.stringify(value.location) : null,
      req.tenantId
    ];

    const { rows } = await pool.query(q, vals);
    const row = rows[0];

    if (typeof notifyProposalSubmitted === "function" && NOTIFY_ENABLED) {
      try { await notifyProposalSubmitted(row); } catch (e) { console.warn("notifyProposalSubmitted failed:", e); }
    }

    return res.json(toCamel(row));
  } catch (err) {
    console.error("POST /proposals error:", err);
    return res.status(500).json({ error: err.message || "Failed to create proposal" });
  }
});

// Owner/Admin can edit a proposal (partial)
app.patch("/proposals/:id", adminOrProposalOwnerGuard, async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid proposal id" });

    const { error, value } = proposalUpdateSchema.validate(req.body || {}, { abortEarly: false });
    if (error) return res.status(400).json({ error: error.message });

    // Map JS keys -> DB columns
    const map = {
      orgName: 'org_name',
      title: 'title',
      summary: 'summary',
      contact: 'contact',
      address: 'address',
      city: 'city',
      country: 'country',
      amountUSD: 'amount_usd',
      ownerEmail: 'owner_email',
      ownerPhone: 'owner_phone',
      docs: 'docs',
    };

    const sets = [];
    const vals = [];
    let i = 1;

    for (const [k, v] of Object.entries(value)) {
      const col = map[k];
      if (!col) continue;
      if (k === 'docs') {
        sets.push(`${col}=$${i++}`);
        vals.push(JSON.stringify(v || []));
      } else {
        sets.push(`${col}=$${i++}`);
        vals.push(v);
      }
    }

    if (sets.length === 0) return res.status(400).json({ error: "No valid fields to update" });

    // Always bump updated_at
    sets.push(`updated_at=NOW()`);

    const sql = `UPDATE proposals SET ${sets.join(', ')} WHERE proposal_id=$${i} AND tenant_id=$${i + 1} RETURNING *`;
    vals.push(id);
    vals.push(req.tenantId);

    const { rows } = await pool.query(sql, vals);
    if (!rows[0]) return res.status(404).json({ error: "Proposal not found" });

    res.json(toCamel(rows[0]));
  } catch (err) {
    console.error("PATCH /proposals/:id error", err);
    res.status(500).json({ error: "Failed to update proposal" });
  }
});

// Approve proposal
app.post("/proposals/:id/approve", adminGuard, async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid id" });
    const { rows } = await pool.query(
      `UPDATE proposals SET status='approved' WHERE proposal_id=$1 AND tenant_id=$2 RETURNING *`,
      [id, req.tenantId]
    );
    if (rows.length === 0) return res.status(404).json({ error: "Proposal not found" });
    res.json(toCamel(rows[0]));
  } catch (err) {
    console.error("Error approving proposal:", err);
    res.status(500).json({ error: "Failed to approve proposal" });
  }
});

// Reject proposal (+ notify admins & proposer)
app.post("/proposals/:id/reject", adminGuard, async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid id" });

    // Optional reason from UI: { reason: "Doesn’t meet scope" }
    const reason = String(req.body?.reason || req.body?.note || "").trim() || null;

    const { rows } = await pool.query(
      `UPDATE proposals SET status='rejected', updated_at = NOW()
         WHERE proposal_id=$1 AND tenant_id=$2
       RETURNING *`,
      [id, req.tenantId]
    );
    if (rows.length === 0) return res.status(404).json({ error: "Proposal not found" });

    const row = rows[0];

    // fire-and-forget notifications
    if (typeof notifyProposalRejected === "function") {
      notifyProposalRejected(row, reason).catch(() => null);
    }

    return res.json(toCamel(row));
  } catch (err) {
    console.error("Error rejecting proposal:", err);
    return res.status(500).json({ error: "Failed to reject proposal" });
  }
});

// Archive proposal
app.post("/proposals/:id/archive", adminGuard, async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid id" });
    const { rows } = await pool.query(
      `UPDATE proposals SET status='archived' WHERE proposal_id=$1 AND tenant_id=$2 RETURNING *`,
      [id, req.tenantId]
    );
    if (rows.length === 0) return res.status(404).json({ error: "Proposal not found" });
    res.json(toCamel(rows[0]));
  } catch (err) {
    console.error("Error archiving proposal:", err);
    res.status(500).json({ error: "Failed to archive proposal" });
  }
});

// Delete proposal
app.delete("/proposals/:id", adminGuard, async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid id" });
    const { rowCount } = await pool.query(
      `DELETE FROM proposals WHERE proposal_id=$1 AND tenant_id=$2`,
      [id, req.tenantId]
    );
    if (rowCount === 0) return res.status(404).json({ error: "Proposal not found" });
    res.json({ success: true });
  } catch (err) {
    console.error("Error deleting proposal:", err);
    res.status(500).json({ error: "Failed to delete proposal" });
  }
});

/// /admin/entities — REPLACE ENTIRE ROUTE (excludes wallets in vendor_profiles; includes proposer_profiles even with 0 proposals)
app.get('/admin/entities', adminGuard, async (req, res) => {
  try {
    const includeArchived = ['true', '1', 'yes'].includes(
      String(req.query.includeArchived || '').toLowerCase()
    );

    const sql = `
      WITH vendor_wallets AS (
        SELECT DISTINCT LOWER(wallet_address) AS w
        FROM vendor_profiles
        WHERE tenant_id = $1
      ),
      props AS (
        SELECT
          LOWER(COALESCE(p.owner_wallet,''))                       AS owner_wallet,
          COALESCE(MAX(NULLIF(p.org_name,'')), '')                 AS entity_name,
          COUNT(*)::int                                            AS proposals_count,
          MAX(COALESCE(p.updated_at, p.created_at))               AS last_proposal_at,

          -- FIX: Use LOWER(TRIM()) for safer checks
          COALESCE(SUM(CASE WHEN LOWER(TRIM(p.status)) IN ('approved','funded','completed')
                            THEN COALESCE(p.amount_usd,0) ELSE 0 END),0)::numeric AS total_awarded_usd,

          -- FIX: Count 'funded' and 'completed' as approved too; use LOWER(TRIM())
          COUNT(*) FILTER (WHERE LOWER(TRIM(p.status)) IN ('approved', 'funded', 'completed'))::int AS approved_count,

          -- FIX: Handle pending case-insensitively
          COUNT(*) FILTER (WHERE LOWER(TRIM(p.status)) = 'pending')::int       AS pending_count,

          -- FIX: Handle rejected case-insensitively
          COUNT(*) FILTER (WHERE LOWER(TRIM(p.status)) = 'rejected')::int      AS rejected_count,

          -- EMAIL: prefer owner_email; else extract from 'contact' if it contains an email
          MAX(
            COALESCE(
              NULLIF(p.owner_email,''),
              NULLIF(
                SUBSTRING(p.contact FROM '([A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\\.[A-Za-z]{2,})'),
                ''
              )
            )
          )                                                        AS email,

          MAX(NULLIF(p.owner_phone,''))                           AS phone,
          MAX(NULLIF(p.owner_telegram_chat_id::text,''))          AS telegram_chat_id,
          MAX(NULLIF(p.owner_telegram_username,''))               AS telegram_username,

          MAX(NULLIF(p.address,''))                               AS address_raw,
          MAX(NULLIF(p.city,''))                                  AS city,
          MAX(NULLIF(p.country,''))                               AS country,

          COUNT(*) FILTER (WHERE p.status = 'archived')::int      AS archived_count,
          COUNT(*) FILTER (WHERE p.status <> 'archived')::int     AS active_count
        FROM proposals p
        WHERE NOT EXISTS (SELECT 1 FROM vendor_wallets vw WHERE vw.w = LOWER(p.owner_wallet))
          AND tenant_id = $1
        GROUP BY LOWER(COALESCE(p.owner_wallet,''))
      ),
      ents AS (
        SELECT
          LOWER(pp.wallet_address)            AS wallet_address,
          COALESCE(pp.org_name,'')            AS org_name,
          NULLIF(pp.contact_email,'')         AS contact_email,
          NULLIF(pp.phone,'')                 AS phone,
          NULLIF(pp.website,'')               AS website,
          NULLIF(pp.address,'')               AS address_raw,
          NULLIF(pp.city,'')                  AS city,
          NULLIF(pp.country,'')               AS country,
          NULLIF(pp.telegram_chat_id::text,'')AS telegram_chat_id,
          NULLIF(pp.telegram_username,'')     AS telegram_username,
          NULLIF(pp.whatsapp,'')              AS whatsapp,
          COALESCE(pp.status,'active')        AS status,
          pp.updated_at                       AS updated_at
        FROM proposer_profiles pp
        WHERE NOT EXISTS (SELECT 1 FROM vendor_wallets vw WHERE vw.w = LOWER(pp.wallet_address))
          AND tenant_id = $1
      ),
      combined AS (
        SELECT
          COALESCE(ents.wallet_address, props.owner_wallet)                AS owner_wallet,
          COALESCE(NULLIF(ents.org_name,''), props.entity_name, '')       AS entity_name,
          COALESCE(ents.contact_email, props.email)                       AS email,
          COALESCE(ents.phone, props.phone)                               AS phone,
          COALESCE(ents.telegram_chat_id, props.telegram_chat_id)         AS telegram_chat_id,
          COALESCE(ents.telegram_username, props.telegram_username)       AS telegram_username,
          COALESCE(ents.address_raw, props.address_raw)                   AS address_raw,
          COALESCE(ents.city, props.city)                                 AS city,
          COALESCE(ents.country, props.country)                           AS country,
          COALESCE(props.proposals_count, 0)::int                         AS proposals_count,

          -- Pass counts through from props CTE
          COALESCE(props.approved_count, 0)::int                          AS approved_count,
          COALESCE(props.pending_count, 0)::int                           AS pending_count,
          COALESCE(props.rejected_count, 0)::int                          AS rejected_count,

          COALESCE(props.last_proposal_at, ents.updated_at)               AS last_activity_at,
          COALESCE(props.total_awarded_usd, 0)::numeric                   AS total_awarded_usd,
          COALESCE(props.archived_count, 0)::int                          AS archived_count,
          COALESCE(props.active_count, 0)::int                            AS active_count,
          COALESCE(ents.status,'active')                                  AS entity_status
        FROM props
        FULL OUTER JOIN ents
          ON ents.wallet_address = props.owner_wallet
      )
      SELECT
        owner_wallet,
        entity_name,
        email,
        phone,
        telegram_chat_id,
        telegram_username,
        address_raw,
        city,
        country,
        proposals_count,
        approved_count, -- Select these in final query
        pending_count,
        rejected_count,
        last_activity_at,
        total_awarded_usd,
        archived_count,
        active_count,
        CASE
          WHEN entity_status = 'archived' THEN TRUE
          WHEN proposals_count > 0 AND active_count = 0 THEN TRUE
          ELSE FALSE
        END AS archived
      FROM combined
      ${includeArchived ? '' : 'WHERE NOT (CASE WHEN entity_status = \'archived\' THEN TRUE WHEN proposals_count > 0 AND active_count = 0 THEN TRUE ELSE FALSE END)'}
      ORDER BY last_activity_at DESC NULLS LAST, entity_name ASC
    `;

    const { rows } = await pool.query(sql, [req.tenantId]);
    const norm = (s) => (typeof s === 'string' && s.trim() !== '' ? s.trim() : null);

    const items = rows.map((r) => {
      const email = norm(r.email);
      const phone = norm(r.phone);
      const line1 = norm(r.address_raw);
      const city = norm(r.city);
      const country = norm(r.country);
      const flat = [line1, city, country].filter(Boolean).join(', ') || null;
      const telegramChatId = norm(r.telegram_chat_id);
      const telegramUsername = norm(r.telegram_username);

      return {
        entityName: r.entity_name || '',
        entity: r.entity_name || '',
        orgName: r.entity_name || '',
        organization: r.entity_name || '',

        walletAddress: r.owner_wallet || '',
        ownerWallet: r.owner_wallet || '',

        proposalsCount: Number(r.proposals_count) || 0,
        lastActivityAt: r.last_activity_at,
        totalBudgetUSD: Number(r.total_awarded_usd) || 0,

        // FIX: Map the counts to the JSON response
        approvedCount: Number(r.approved_count) || 0,
        pendingCount: Number(r.pending_count) || 0,
        rejectedCount: Number(r.rejected_count) || 0,
        archivedCount: Number(r.archived_count) || 0,

        email,
        contactEmail: email,
        ownerEmail: email,
        phone,
        whatsapp: phone,

        telegramChatId: telegramChatId,
        telegramUsername: telegramUsername,
        telegramConnected: !!(telegramChatId || telegramUsername),
        ownerTelegramUsername: telegramUsername,
        ownerTelegramChatId: telegramChatId,

        address: flat,
        addressText: flat,
        address1: line1,

        archived: !!r.archived,
      };
    });

    res.json({ items, page: 1, pageSize: items.length, total: items.length });
  } catch (e) {
    console.error('GET /admin/entities error', e);
    res.status(500).json({ error: 'Failed to list entities' });
  }
});

app.get("/proposer-profile", authGuard, async (req, res) => {
  try {
    const wallet = String(req.user?.sub || "").toLowerCase();
    if (!wallet) return res.status(401).json({ error: "Unauthorized" });

    const { rows } = await pool.query(
      `SELECT * FROM proposer_profiles WHERE lower(wallet_address)=lower($1)`,
      [wallet]
    );

    if (rows[0]) {
      return res.json(toCamel(rows[0]));
    } else {
      // Return empty profile if none exists
      return res.json({
        walletAddress: wallet,
        orgName: "",
        contactEmail: "",
        phone: "",
        website: "",
        address: "",
        city: "",
        country: "",
        telegramChatId: "",
        whatsapp: "",
        status: "active"
      });
    }
  } catch (err) {
    console.error("GET /proposer-profile error:", err);
    return res.status(500).json({ error: "Failed to load profile" });
  }
});

// Create or update proposer profile
app.post("/proposer-profile", authGuard, async (req, res) => {
  try {
    const wallet = String(req.user?.sub || "").toLowerCase();
    if (!wallet) return res.status(401).json({ error: "Unauthorized" });

    const {
      orgName,
      contactEmail,
      phone,
      website,
      address,
      city,
      country,
      telegramChatId,
      whatsapp
    } = req.body;

    // Validate required fields
    if (!orgName?.trim()) {
      return res.status(400).json({ error: "Organization name is required" });
    }

    if (!contactEmail?.trim()) {
      return res.status(400).json({ error: "Contact email is required" });
    }

    const { rows } = await pool.query(
      `INSERT INTO proposer_profiles
        (wallet_address, org_name, contact_email, phone, website, address, city, country, telegram_chat_id, whatsapp, updated_at)
       VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, NOW())
       ON CONFLICT (wallet_address)
       DO UPDATE SET
         org_name = EXCLUDED.org_name,
         contact_email = EXCLUDED.contact_email,
         phone = EXCLUDED.phone,
         website = EXCLUDED.website,
         address = EXCLUDED.address,
         city = EXCLUDED.city,
         country = EXCLUDED.country,
         telegram_chat_id = EXCLUDED.telegram_chat_id,
         whatsapp = EXCLUDED.whatsapp,
         updated_at = NOW()
       RETURNING *`,
      [wallet, orgName, contactEmail, phone, website, address, city, country, telegramChatId, whatsapp]
    );

    // Also update user_profiles for backward compatibility
    await pool.query(
      `INSERT INTO user_profiles
        (wallet_address, display_name, email, phone, website, address, city, country, telegram_chat_id, whatsapp, updated_at)
       VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, NOW())
       ON CONFLICT (wallet_address)
       DO UPDATE SET
         display_name = EXCLUDED.display_name,
         email = EXCLUDED.email,
         phone = EXCLUDED.phone,
         website = EXCLUDED.website,
         address = EXCLUDED.address,
         city = EXCLUDED.city,
         country = EXCLUDED.country,
         telegram_chat_id = EXCLUDED.telegram_chat_id,
         whatsapp = EXCLUDED.whatsapp,
         updated_at = NOW()`,
      [wallet, orgName, contactEmail, phone, website, address, city, country, telegramChatId, whatsapp]
    );

    return res.json(toCamel(rows[0]));
  } catch (err) {
    console.error("POST /proposer-profile error:", err);
    return res.status(500).json({ error: "Failed to save profile" });
  }
});

// Get current user's profile (unified - tries both tables)
app.get("/user-profile", authGuard, async (req, res) => {
  try {
    const wallet = String(req.user?.sub || "").toLowerCase();
    if (!wallet) return res.status(401).json({ error: "Unauthorized" });

    // Try proposer_profiles first, then user_profiles
    const { rows: proposerRows } = await pool.query(
      `SELECT * FROM proposer_profiles WHERE lower(wallet_address)=lower($1)`,
      [wallet]
    );

    if (proposerRows[0]) {
      return res.json(toCamel(proposerRows[0]));
    }

    const { rows: userRows } = await pool.query(
      `SELECT * FROM user_profiles WHERE lower(wallet_address)=lower($1)`,
      [wallet]
    );

    if (userRows[0]) {
      return res.json(toCamel(userRows[0]));
    }

    // Return empty profile structure
    return res.json({
      walletAddress: wallet,
      orgName: "",
      displayName: "",
      email: "",
      phone: "",
      website: "",
      address: "",
      city: "",
      country: "",
      telegramChatId: "",
      whatsapp: ""
    });
  } catch (err) {
    console.error("GET /user-profile error:", err);
    return res.status(500).json({ error: "Failed to load profile" });
  }
});


// ==============================
// Routes — Bids
// ==============================
app.get("/bids", async (req, res) => {
  try {
    const pid = Number(req.query.proposalId);

    // role / caller (if your auth middleware sets req.user)
    const role = (req.user?.role || "guest").toLowerCase();
    const caller = (req.user?.sub || "").toLowerCase();

    // --- PUBLIC PAGE (guest + specific proposal) — keep sanitized shape ---
    if (SCOPE_BIDS_FOR_VENDOR && role !== 'admin' && !caller && Number.isFinite(pid)) {
      const { rows } = await pool.query(
        `SELECT bid_id, proposal_id, vendor_name, price_usd, days, status, created_at, updated_at, milestones
           FROM bids
          WHERE proposal_id = $1 AND status <> 'archived' AND tenant_id = $2
          ORDER BY bid_id DESC`,
        [pid, req.tenantId]
      );

      // keep the public sanitized payload (no payment metadata here)
      const out = rows.map(r => {
        const ms = Array.isArray(r.milestones)
          ? r.milestones
          : (typeof r.milestones === 'string' ? JSON.parse(r.milestones || '[]') : []);
        return {
          bidId: r.bid_id,
          proposalId: r.proposal_id,
          vendorName: r.vendor_name,
          priceUSD: Number(r.price_usd),
          days: r.days,
          status: r.status,
          createdAt: r.created_at,
          updatedAt: r.updated_at,
          milestones: ms.map(m => ({
            name: m?.name,
            amount: Number(m?.amount ?? 0),
            dueDate: m?.dueDate ?? m?.due_date ?? null,
            completed: !!m?.completed
          }))
        };
      });

      return res.json(out);
    }

    // --- VENDOR-SCOPED (non-admin) ---
    if (SCOPE_BIDS_FOR_VENDOR && role !== "admin") {
      if (!caller) return res.status(401).json({ error: "Unauthorized" });

      if (Number.isFinite(pid)) {
        const { rows } = await pool.query(
          "SELECT * FROM bids WHERE lower(wallet_address)=lower($1) AND proposal_id=$2 AND tenant_id=$3 ORDER BY bid_id DESC",
          [caller, pid, req.tenantId]
        );
        const hydrated = await Promise.all(rows.map(r => overlayPaidFromMp(r, pool)));
        return res.json(mapRows(hydrated));
      } else {
        const { rows } = await pool.query(
          "SELECT * FROM bids WHERE lower(wallet_address)=lower($1) AND tenant_id=$2 ORDER BY bid_id DESC",
          [caller, req.tenantId]
        );
        const hydrated = await Promise.all(rows.map(r => overlayPaidFromMp(r, pool)));
        return res.json(mapRows(hydrated));
      }
    }

    // --- ADMIN (or flag OFF): return all bids, hydrated ---
    if (Number.isFinite(pid)) {
      const { rows } = await pool.query(
        "SELECT * FROM bids WHERE proposal_id=$1 AND tenant_id=$2 ORDER BY bid_id DESC",
        [pid, req.tenantId]
      );
      const hydrated = await Promise.all(rows.map(r => overlayPaidFromMp(r, pool)));
      return res.json(mapRows(hydrated));
    } else {
      const { rows } = await pool.query("SELECT * FROM bids WHERE tenant_id=$1 ORDER BY bid_id DESC", [req.tenantId]);
      const hydrated = await Promise.all(rows.map(r => overlayPaidFromMp(r, pool)));
      return res.json(mapRows(hydrated));
    }
  } catch (err) {
    res.status(500).json({ error: err.message || "Failed to load bids" });
  }
});

app.get("/bids/:id", async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid bid id" });

  try {
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1 AND tenant_id=$2", [id, req.tenantId]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });

    const bid = rows[0];

    // enforce ownership when flag ON and not admin
    const role = (req.user?.role || "guest").toLowerCase();
    const caller = (req.user?.sub || "").toLowerCase();
    if (SCOPE_BIDS_FOR_VENDOR && role !== "admin") {
      if (!caller) return res.status(401).json({ error: "Unauthorized" });
      if ((bid.wallet_address || "").toLowerCase() !== caller) {
        return res.status(403).json({ error: "Forbidden" });
      }
    }

    // ★ Hydrate this single bid from milestone_payments (brings Safe 'paid' into milestones)
    const hydrated = await overlayPaidFromMp(bid, pool);

    // keep your existing shape/casing
    return res.json(toCamel(hydrated));
  } catch (err) {
    return res.status(500).json({ error: err.message || "Failed to load bid" });
  }
});

// Inline analysis on creation
app.post("/bids", requireApprovedVendorOrAdmin, async (req, res) => {
  try {
    // validate request
    const { error, value } = bidSchema.validate(req.body);
    if (error) return res.status(400).json({ error: error.message });

    // Sanitize filenames to prevent DB/PDF errors
    if (Array.isArray(value.files)) {
      value.files.forEach(f => {
        if (f && typeof f.name === 'string') {
          // Remove control characters and other weirdness
          f.name = f.name.replace(/[\x00-\x1F\x7F]/g, "").trim();
        }
      });
    }
    if (value.doc && typeof value.doc.name === 'string') {
      value.doc.name = value.doc.name.replace(/[\x00-\x1F\x7F]/g, "").trim();
    }

    // pick a doc for back-compat/Agent2 (prefer PDF from files, else first file, else provided doc)
    const docCompat =
      value.doc ||
      (Array.isArray(value.files) &&
        (value.files.find(f => /\.pdf($|\?)/i.test(String(f?.name || ""))) || value.files[0])) ||
      null;

    let inserted; // ← declare once

    const insertQ = `
      INSERT INTO bids (
        proposal_id,
        vendor_name,
        price_usd,
        days,
        notes,
        wallet_address,
        preferred_stablecoin,
        milestones,
        doc,
        files,
        status,
        created_at,
        tenant_id
      )
      VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,'pending', NOW(), $11)
      RETURNING *`;

    const insertVals = [
      value.proposalId,
      value.vendorName,
      value.priceUSD,
      value.days,
      value.notes,
      value.walletAddress,
      value.preferredStablecoin,
      JSON.stringify(value.milestones || []),
      docCompat ? JSON.stringify(docCompat) : null, // back-compat single doc
      JSON.stringify(value.files || []),            // multi-file column
      req.tenantId
    ];

    const { rows } = await pool.query(insertQ, insertVals);
    inserted = rows[0];

    // fetch proposal
    const { rows: pr } = await pool.query(
      "SELECT * FROM proposals WHERE proposal_id=$1",
      [inserted.proposal_id]
    );
    const prop = pr[0] || null;

    // inline Agent2 analysis with deadline
    const INLINE_ANALYSIS_DEADLINE_MS = Number(process.env.AGENT2_INLINE_TIMEOUT_MS || 12000);

    const analysis = await withTimeout(
      prop
        ? runAgent2OnBid(inserted, prop, { tenantId: req.tenantId })
        : Promise.resolve({
          status: "error",
          summary: "Proposal not found for analysis.",
          risks: [],
          fit: "low",
          milestoneNotes: [],
          confidence: 0,
          pdfUsed: false,
          pdfChars: 0,
          pdfSnippet: null,
          pdfDebug: { reason: "proposal_missing" },
        }),
      INLINE_ANALYSIS_DEADLINE_MS,
      () => ({
        status: "error",
        summary: "Agent2 timed out during inline analysis.",
        risks: [],
        fit: "low",
        milestoneNotes: [],
        confidence: 0,
        pdfUsed: false,
        pdfChars: 0,
        pdfSnippet: null,
        pdfDebug: { reason: "inline_timeout" },
      })
    );

    await pool.query(
      "UPDATE bids SET ai_analysis=$1 WHERE bid_id=$2",
      [JSON.stringify(analysis), inserted.bid_id]
    );
    inserted.ai_analysis = analysis;

    // vendor + proposal for notifications
    const [{ rows: vp }, { rows: prj }] = await Promise.all([
      pool.query(
        "SELECT * FROM vendor_profiles WHERE lower(wallet_address)=lower($1)",
        [inserted.wallet_address]
      ),
      pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [inserted.proposal_id]),
    ]);
    const vendor = vp[0] || null;
    const proposal = prj[0] || null;

    if (typeof notifyBidSubmitted === "function") {
      notifyBidSubmitted(inserted, proposal, vendor).catch(() => null);
    }

    // audit
    try {
      const actorWallet = (req.user && (req.user.address || req.user.sub)) || null;
      const actorRole = (req.user && req.user.role) || "vendor";

      const ins = await pool.query(
        `INSERT INTO bid_audits (bid_id, actor_wallet, actor_role, changes)
         VALUES ($1,$2,$3,$4)
         RETURNING audit_id`,
        [Number(inserted.bid_id ?? inserted.id), actorWallet, actorRole, { created: true }]
      );
      if (typeof enrichAuditRow === "function") {
        enrichAuditRow(pool, ins.rows[0].audit_id, pinataUploadFile).catch(() => null);
      }
    } catch { }

    return res.status(201).json(toCamel(inserted));
  } catch (err) {
    console.error("POST /bids error:", err);
    return res.status(500).json({ error: err.message });
  }
});

// Approve / award bid (+ notify admin & vendor)
app.post("/bids/:id/approve", adminGuard, async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid bid id" });

  try {
    // 1) Update status -> approved
    const { rows } = await pool.query(
      `UPDATE bids SET status='approved', updated_at=NOW() WHERE bid_id=$1 AND tenant_id=$2 RETURNING *`,
      [id, req.tenantId]
    );
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });
    const bid = rows[0];
    await writeAudit(id, req, { status: { to: 'approved' } });

    // 2) Pull proposal + vendor profile for contacts
    const [{ rows: prjRows }, { rows: vpRows }] = await Promise.all([
      pool.query(`SELECT * FROM proposals WHERE proposal_id=$1`, [bid.proposal_id]),
      pool.query(`SELECT * FROM vendor_profiles WHERE LOWER(wallet_address)=LOWER($1)`, [bid.wallet_address])
    ]);
    const proposal = prjRows[0] || null;
    const vendor = vpRows[0] || null;

    // 3) Fire-and-forget notifications
    if (typeof notifyBidApproved === "function") {
      notifyBidApproved(bid, proposal, vendor).catch(() => null);
    }

    return res.json(toCamel(bid));
  } catch (err) {
    console.error("approve bid error", err);
    return res.status(500).json({ error: "Internal error approving bid" });
  }
});

// Reject bid (+ notify admin & vendor)
app.post("/bids/:id/reject", adminGuard, async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid bid id" });

  try {
    // Optional reason from UI
    const reason = String(req.body?.reason || req.body?.note || "").trim() || null;

    // 1) Update status -> rejected
    const { rows } = await pool.query(
      `UPDATE bids SET status='rejected', updated_at=NOW() WHERE bid_id=$1 AND tenant_id=$2 RETURNING *`,
      [id, req.tenantId]
    );
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });
    const bid = rows[0];
    await writeAudit(id, req, { status: { to: 'rejected' }, reason });

    // 2) Pull proposal + vendor profile for contacts
    const [{ rows: prjRows }, { rows: vpRows }] = await Promise.all([
      pool.query(`SELECT * FROM proposals WHERE proposal_id=$1`, [bid.proposal_id]),
      pool.query(`SELECT * FROM vendor_profiles WHERE LOWER(wallet_address)=LOWER($1)`, [bid.wallet_address])
    ]);
    const proposal = prjRows[0] || null;
    const vendor = vpRows[0] || null;

    // 3) Fire-and-forget notifications
    if (typeof notifyBidRejected === "function") {
      notifyBidRejected(bid, proposal, vendor, reason).catch(() => null);
    }

    return res.json(toCamel(bid));
  } catch (err) {
    console.error("reject bid error", err);
    return res.status(500).json({ error: "Internal error rejecting bid" });
  }
});

app.post("/bids/:id/archive", adminGuard, async (req, res) => {
  const { id } = req.params;
  try {
    const { rows } = await pool.query(
      `UPDATE bids SET status = 'archived'
       WHERE bid_id = $1 AND tenant_id = $2
       RETURNING *`,
      [id, req.tenantId]
    );
    if (!rows.length) return res.status(404).json({ error: "Bid not found" });
    res.json(toCamel(rows[0]));
  } catch (err) {
    console.error("Error archiving bid:", err);
    res.status(500).json({ error: "Failed to archive bid" });
  }
});

app.delete("/bids/:id", adminGuard, async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid bid id" });
  try {
    const { rowCount } = await pool.query(`DELETE FROM bids WHERE bid_id=$1 AND tenant_id=$2`, [id, req.tenantId]);
    if (rowCount === 0) return res.status(404).json({ error: "Bid not found" });
    return res.json({ success: true });
  } catch (err) {
    console.error("delete bid error", err);
    return res.status(500).json({ error: "Failed to delete bid" });
  }
});

app.patch("/bids/:id", adminGuard, async (req, res) => {
  const bidId = Number(req.params.id);
  if (!Number.isFinite(bidId)) {
    return res.status(400).json({ error: "Invalid bid id" });
  }

  // Whitelisted edits
  let { status, preferredStablecoin, priceUSD, days, notes } = req.body || {};

  try {
    // 1) Load current row (to compute from->to changes); lock lightly to prevent races
    const { rows: currentRows } = await pool.query(
      `SELECT bid_id, status, preferred_stablecoin, price_usd, days, notes
         FROM bids
        WHERE bid_id = $1 AND tenant_id = $2`,
      [bidId, req.tenantId]
    );
    const current = currentRows[0];
    if (!current) return res.status(404).json({ error: "Bid not found" });

    // 2) Build UPDATE SET and validate
    const set = [];
    const vals = [bidId]; // $1 = bid_id
    let i = 1;

    // status
    if (status !== undefined) {
      const v = String(status).toLowerCase();
      if (!["approved", "rejected"].includes(v)) {
        return res.status(400).json({ error: 'Invalid status; expected "approved" or "rejected"' });
      }
      set.push(`status = $${++i}`); vals.push(v);
    }

    // preferred_stablecoin
    if (preferredStablecoin !== undefined) {
      const v = String(preferredStablecoin || "").toUpperCase();
      if (!["USDC", "USDT"].includes(v)) {
        return res.status(400).json({ error: "preferredStablecoin must be USDC or USDT" });
      }
      set.push(`preferred_stablecoin = $${++i}`); vals.push(v);
    }

    // price_usd
    if (priceUSD !== undefined) {
      const v = Number(priceUSD);
      if (!Number.isFinite(v) || v < 0) return res.status(400).json({ error: "Invalid priceUSD" });
      set.push(`price_usd = $${++i}`); vals.push(v);
    }

    // days
    if (days !== undefined) {
      const v = Number(days);
      if (!Number.isFinite(v) || v < 0) return res.status(400).json({ error: "Invalid days" });
      set.push(`days = $${++i}`); vals.push(v);
    }

    // notes
    if (notes !== undefined) {
      if (typeof notes !== "string") return res.status(400).json({ error: "Invalid notes" });
      set.push(`notes = $${++i}`); vals.push(notes);
    }

    if (set.length === 0) {
      return res.status(400).json({ error: "No editable fields provided" });
    }

    // 3) Perform UPDATE
    const sqlUpdate = `
      UPDATE bids
         SET ${set.join(", ")}, updated_at = NOW()  -- keep if you added updated_at; otherwise remove
       WHERE bid_id = $1 AND tenant_id = $${i + 1}
   RETURNING *`;
    vals.push(req.tenantId);
    const { rows: updatedRows } = await pool.query(sqlUpdate, vals);
    const updated = updatedRows[0];

    // 4) Build audit JSON — include only actually changed keys
    const changes = {};
    const map = {
      status: "status",
      preferredStablecoin: "preferred_stablecoin",
      priceUSD: "price_usd",
      days: "days",
      notes: "notes",
    };

    if (status !== undefined && current.status !== updated.status) {
      changes["status"] = { from: current.status, to: updated.status };
    }
    if (preferredStablecoin !== undefined && current.preferred_stablecoin !== updated.preferred_stablecoin) {
      changes["preferred_stablecoin"] = {
        from: current.preferred_stablecoin,
        to: updated.preferred_stablecoin,
      };
    }
    if (priceUSD !== undefined && Number(current.price_usd) !== Number(updated.price_usd)) {
      changes["price_usd"] = { from: Number(current.price_usd), to: Number(updated.price_usd) };
    }
    if (days !== undefined && Number(current.days) !== Number(updated.days)) {
      changes["days"] = { from: Number(current.days), to: Number(updated.days) };
    }
    if (notes !== undefined && String(current.notes || "") !== String(updated.notes || "")) {
      changes["notes"] = { from: current.notes || null, to: updated.notes || null };
    }

    // Only write an audit row if something actually changed
    if (Object.keys(changes).length > 0) {
      const actorWallet = req.user?.sub || null;  // your JWT puts wallet in sub
      const actorRole = req.user?.role || "admin";
      // AFTER (correct)
      const ins = await pool.query(
        'INSERT INTO bid_audits (bid_id, actor_wallet, actor_role, changes) VALUES ($1,$2,$3,$4) RETURNING audit_id',
        [bidId, actorWallet, actorRole, changes]
      );
      enrichAuditRow(pool, ins.rows[0].audit_id, pinataUploadFile).catch(/* ... */);
    }

    // Return normalized bid
    return res.json(toCamel(updated));
  } catch (err) {
    console.error("PATCH /bids/:id failed", { bidId, body: req.body, err });
    if (err?.code === "42703") {
      return res.status(400).json({
        error: "DB column not found. Ensure columns exist: preferred_stablecoin, price_usd, days, notes, updated_at (optional).",
      });
    }
    return res.status(500).json({ error: "Internal error updating bid" });
  }
});

// ADD RIGHT HERE
app.patch('/bids/:id/notes', requireApprovedVendorOrAdmin, async (req, res) => {
  try {
    const bidId = Number(req.params.id);
    const { notes } = req.body;

    await pool.query(
      `UPDATE bids SET notes = $1 WHERE bid_id = $2 AND tenant_id = $3`,
      [notes, bidId, req.tenantId]
    );

    res.json({ ok: true });
  } catch (e) {
    console.error('Error updating bid notes:', e);
    res.status(500).json({ error: 'failed_update_notes' });
  }
});

// Admin: replace milestones array on a bid
app.patch("/bids/:id/milestones", adminGuard, async (req, res) => {
  const bidId = Number(req.params.id);
  if (!Number.isFinite(bidId)) return res.status(400).json({ error: "Invalid bid id" });

  const incoming = req.body?.milestones;
  if (!Array.isArray(incoming)) {
    return res.status(400).json({ error: "milestones must be an array" });
  }

  // Normalize + validate
  const norm = incoming.map((m, i) => ({
    name: String(m?.name ?? `Milestone ${i + 1}`),
    amount: Number(m?.amount ?? 0),
    dueDate: new Date(m?.dueDate ?? m?.due_date ?? Date.now()).toISOString(),
    completed: !!m?.completed,
    completionDate: m?.completionDate ?? null,
    proof: m?.proof ?? "",
    paymentTxHash: m?.paymentTxHash ?? null,
    paymentDate: m?.paymentDate ?? null,
  }));

  if (norm.some(m => !Number.isFinite(m.amount) || m.amount < 0)) {
    return res.status(400).json({ error: "All milestone amounts must be non-negative numbers" });
  }

  try {
    // Load current for audit
    const { rows: curRows } = await pool.query(
      `SELECT bid_id, milestones, price_usd FROM bids WHERE bid_id=$1 AND tenant_id=$2`,
      [bidId, req.tenantId]
    );
    const current = curRows[0];
    if (!current) return res.status(404).json({ error: "Bid not found" });

    // (Optional) Enforce sum === bid price
    // const sum = norm.reduce((s, m) => s + Number(m.amount || 0), 0);
    // if (Number(current.price_usd) !== sum) {
    //   return res.status(400).json({ error: `Sum of milestone amounts (${sum}) must equal bid price (${current.price_usd})` });
    // }

    const { rows: upd } = await pool.query(
      `UPDATE bids
         SET milestones = $2::jsonb
       WHERE bid_id = $1 AND tenant_id = $3
       RETURNING *`,
      [bidId, JSON.stringify(norm), req.tenantId]
    );

    // Audit row
    const actorWallet = req.user?.sub || req.user?.address || null;
    const actorRole = req.user?.role || "admin";

    const ins = await pool.query(
      `INSERT INTO bid_audits (bid_id, actor_wallet, actor_role, changes)
   VALUES ($1, $2, $3, $4)
   RETURNING audit_id`,
      [bidId, actorWallet, actorRole, { milestones: { from: current.milestones, to: norm } }]
    );

    // fire-and-forget enrichment (IPFS + hash)
    enrichAuditRow(pool, ins.rows[0].audit_id, pinataUploadFile).catch(err =>
      console.error('audit enrich failed:', err)
    );

    return res.json(toCamel(upd[0]));
  } catch (err) {
    console.error("PATCH /bids/:id/milestones failed", { bidId, err });
    return res.status(500).json({ error: "Internal error updating milestones" });
  }
});

// GET /audit?itemType=proposal&itemId=123  OR  /audit?itemType=bid&itemId=456
app.get('/audit', async (req, res) => {
  const itemType = String(req.query.itemType || '').toLowerCase();
  const itemId = Number(req.query.itemId);

  if (!itemType || !Number.isFinite(itemId)) return res.json([]);

  if (itemType === 'bid') {
    const { rows } = await pool.query(
      `SELECT
     ba.created_at,
     ba.actor_role,
     ba.actor_wallet,
     ba.changes,
     ba.ipfs_cid,
     ba.merkle_index,
     ba.merkle_proof,
     ba.batch_id,
     ab.period_id,
     ab.tx_hash,
     ab.contract_addr,
     ab.chain_id
   FROM bid_audits ba
   JOIN bids b ON b.bid_id = ba.bid_id
   LEFT JOIN audit_batches ab ON ab.id = ba.batch_id
   WHERE ba.bid_id = $1 AND b.tenant_id = $2
   ORDER BY ba.created_at DESC`,
      [itemId, req.tenantId]
    );
    return res.json(rows.map(r => ({
      created_at: r.created_at,
      action: 'update',
      actor_role: r.actor_role,
      actor_address: r.actor_wallet,
      changed_fields: Object.keys(r.changes || {}),
      changes: r.changes || {},                 // ← add this line
      ipfs_cid: r.ipfs_cid,
      merkle_index: r.merkle_index ?? null,
      proof: Array.isArray(r.merkle_proof)
        ? r.merkle_proof.map(buf =>
          typeof buf === 'string'
            ? (buf.startsWith('0x') ? buf : '0x' + buf)
            : '0x' + Buffer.from(buf).toString('hex')
        )
        : [],
      batch: r.period_id ? {
        period_id: r.period_id,
        tx_hash: r.tx_hash,
        contract_addr: r.contract_addr,
        chain_id: r.chain_id
      } : null
    })));
  }

  if (itemType === 'proposal') {
    // join through bids to show all bid audits for this proposal
    const { rows } = await pool.query(
      `SELECT
     ba.created_at,
     ba.actor_role,
     ba.actor_wallet,
     ba.changes,
     ba.ipfs_cid,
     ba.merkle_index,
     ba.merkle_proof,
     ba.batch_id,
     ab.period_id,
     ab.tx_hash,
     ab.contract_addr,
     ab.chain_id
   FROM bid_audits ba
   JOIN bids b ON b.bid_id = ba.bid_id
   LEFT JOIN audit_batches ab ON ab.id = ba.batch_id
   WHERE b.proposal_id = $1 AND b.tenant_id = $2
   ORDER BY ba.created_at DESC`,
      [itemId, req.tenantId]
    );
    return res.json(rows.map(r => ({
      created_at: r.created_at,
      action: 'update',
      actor_role: r.actor_role,
      actor_address: r.actor_wallet,
      changed_fields: Object.keys(r.changes || {}),
      changes: r.changes || {},                 // ← add this line
      ipfs_cid: r.ipfs_cid,
      merkle_index: r.merkle_index ?? null,
      proof: Array.isArray(r.merkle_proof)
        ? r.merkle_proof.map(buf =>
          typeof buf === 'string'
            ? (buf.startsWith('0x') ? buf : '0x' + buf)
            : '0x' + Buffer.from(buf).toString('hex')
        )
        : [],
      batch: r.period_id ? {
        period_id: r.period_id,
        tx_hash: r.tx_hash,
        contract_addr: r.contract_addr,
        chain_id: r.chain_id
      } : null
    })));
  }

  res.json([]);
});

// GET /admin/anchor?period=YYYY-MM-DDTHH
// Anchors the specified hour (UTC) on-chain and writes batch/proofs to DB.
app.get('/admin/anchor', async (req, res) => {
  // Manual Auth Check: Support both JWT (Admin) AND Static Secret (Cron Job)
  const authHeader = req.headers.authorization || '';
  const token = authHeader.startsWith('Bearer ') ? authHeader.slice(7) : authHeader;

  let user = verifyJwt(token);
  const isCron = process.env.ANCHOR_SECRET && token === process.env.ANCHOR_SECRET; // Check env var exists too

  console.log(`[Anchor] Auth Check: Token=${token.slice(0, 5)}... isCron=${isCron} User=${user?.sub}`);

  // if (!user && !isCron) {
  //   console.warn('[Anchor] Auth Failed: Invalid token and not cron secret');
  //   return res.status(401).json({ error: 'unauthenticated' });
  // }
  // ^ REVERTED: User says this broke the existing cron job which likely has no auth or uses headers.
  // We allow it to proceed. If it's unauthenticated, it relies on resolveTenant (headers/cookies).

  // If it's the cron job, we might need to assume a default tenant or use a header
  // If it's a user, we use their tenant_id
  if (user) {
    req.user = user;
    // Apply the same fix as authGuard: overwrite default if user has one
    const isDefault = req.tenantId === '00000000-0000-0000-0000-000000000000';
    if ((!req.tenantId || isDefault) && user.tenant_id) {
      req.tenantId = user.tenant_id;
    }
  }

  console.log(`[Anchor] Proceeding with TenantID=${req.tenantId}`);
  try {
    const period = req.query.period ? String(req.query.period) : periodIdForDate();

    // Fetch tenant-specific anchoring config
    const anchorConfig = {
      rpcUrl: await tenantService.getTenantConfig(req.tenantId, 'ANCHOR_RPC_URL'),
      chainId: await tenantService.getTenantConfig(req.tenantId, 'ANCHOR_CHAIN_ID'),
      contractAddr: await tenantService.getTenantConfig(req.tenantId, 'ANCHOR_CONTRACT'),
      privateKey: await tenantService.getTenantConfig(req.tenantId, 'ANCHOR_PRIVATE_KEY'),
    };

    const out = await anchorPeriod(pool, period, req.tenantId, anchorConfig);
    res.json({ ok: true, ...out });
  } catch (e) {
    res.status(500).json({ ok: false, error: String(e.message || e) });
  }
});

// GET /admin/anchor/finalize?period=YYYY-MM-DDTHH&tx=0xTXHASH
// Use this if you already anchored externally; verifies on-chain root and links DB rows.
app.get('/admin/anchor/finalize', async (req, res) => {
  try {
    const period = String(req.query.period || '');
    const tx = req.query.tx ? String(req.query.tx) : null;
    if (!/^\d{4}-\d{2}-\d{2}T\d{2}$/.test(period)) {
      return res.status(400).json({ ok: false, error: 'period must be YYYY-MM-DDTHH (UTC hour)' });
    }

    // Fetch tenant-specific anchoring config
    const anchorConfig = {
      rpcUrl: await tenantService.getTenantConfig(req.tenantId, 'ANCHOR_RPC_URL'),
      chainId: await tenantService.getTenantConfig(req.tenantId, 'ANCHOR_CHAIN_ID'),
      contractAddr: await tenantService.getTenantConfig(req.tenantId, 'ANCHOR_CONTRACT'),
      // privateKey not needed for finalize (read-only verification), but RPC/Contract are
    };

    const out = await finalizeExistingAnchor(pool, period, tx, req.tenantId, anchorConfig);
    res.json({ ok: true, ...out });
  } catch (e) {
    res.status(500).json({ ok: false, error: String(e.message || e) });
  }
});

// GET /admin/anchor/candidates?period=YYYY-MM-DDTHH
app.get('/admin/anchor/candidates', async (req, res) => {
  try {
    const period = String(req.query.period || '');
    if (!/^\d{4}-\d{2}-\d{2}T\d{2}$/.test(period)) {
      return res.status(400).json({ ok: false, error: 'period must be YYYY-MM-DDTHH' });
    }
    const { rows } = await pool.query(
      `SELECT ba.audit_id, ba.bid_id, ba.created_at,
              (ba.ipfs_cid IS NOT NULL) AS has_ipfs,
              (ba.leaf_hash IS NOT NULL) AS has_leaf
         FROM bid_audits ba
         JOIN bids b ON b.bid_id = ba.bid_id
        WHERE ba.batch_id IS NULL
          AND ba.leaf_hash IS NOT NULL
          AND to_char(ba.created_at AT TIME ZONE 'UTC','YYYY-MM-DD"T"HH24') = $1
          AND b.tenant_id = $2
        ORDER BY ba.audit_id ASC`,
      [period, req.tenantId]
    );
    res.type('application/json').json({ ok: true, period, count: rows.length, rows });
  } catch (e) {
    res.status(500).type('application/json').json({ ok: false, error: String(e.message || e) });
  }
});

// GET /admin/anchor/periods — what the API's DB thinks is available to anchor
app.get('/admin/anchor/periods', async (req, res) => {
  try {
    const q = `
      SELECT to_char(ba.created_at AT TIME ZONE 'UTC','YYYY-MM-DD"T"HH24') AS period,
             COUNT(*) AS cnt
      FROM bid_audits ba
      JOIN bids b ON b.bid_id = ba.bid_id
      WHERE ba.leaf_hash IS NOT NULL
        AND ba.batch_id IS NULL
        AND b.tenant_id = $1
      GROUP BY 1
      ORDER BY 1`;
    const { rows } = await pool.query(q, [req.tenantId]);
    res.json({ ok: true, rows });
  } catch (e) {
    res.status(500).json({ ok: false, error: String(e.message || e) });
  }
});

// GET /admin/anchor/last — last few audits the API can see
app.get('/admin/anchor/last', async (req, res) => {
  try {
    const { rows } = await pool.query(`
      SELECT ba.audit_id, ba.bid_id,
             to_char(ba.created_at AT TIME ZONE 'UTC','YYYY-MM-DD"T"HH24:MI:SS') AS created_utc,
             (ba.ipfs_cid IS NOT NULL) AS has_ipfs,
             (ba.leaf_hash IS NOT NULL) AS has_leaf,
             ba.batch_id
      FROM bid_audits ba
      JOIN bids b ON b.bid_id = ba.bid_id
      WHERE b.tenant_id = $1
      ORDER BY ba.audit_id DESC
      LIMIT 10`, [req.tenantId]);
    res.json({ ok: true, rows });
  } catch (e) {
    res.status(500).json({ ok: false, error: String(e.message || e) });
  }
});

app.get('/admin/audit/recent', adminGuard, async (req, res) => {
  try {
    const take = Math.min(parseInt(req.query.take || '50', 10), 200);
    const { rows } = await pool.query(`
      SELECT ba.created_at, ba.actor_role, ba.actor_wallet, ba.changes, ba.bid_id,
             ab.period_id, ab.tx_hash, ab.contract_addr, ab.chain_id
        FROM bid_audits ba
        JOIN bids b ON b.bid_id = ba.bid_id
        LEFT JOIN audit_batches ab ON ab.id = ba.batch_id
       WHERE b.tenant_id = $2
       ORDER BY ba.created_at DESC
       LIMIT $1`, [take, req.tenantId]);
    res.set('Cache-Control', 'no-store');
    res.json(rows);
  } catch (e) {
    res.status(500).json({ error: 'Failed to load recent audit' });
  }
});

app.get('/admin/alerts', adminGuard, async (_req, res) => {
  try {
    const { rows } = await pool.query(`
      SELECT ba.created_at, ba.bid_id, ba.changes
        FROM bid_audits ba
        JOIN bids b ON b.bid_id = ba.bid_id
       WHERE ba.changes ? 'ipfs_missing' AND b.tenant_id = $1
       ORDER BY ba.created_at DESC
       LIMIT 100`, [req.tenantId]);
    res.json(rows.map(r => ({
      type: 'ipfs_missing',
      createdAt: r.created_at,
      bidId: r.bid_id,
      details: r.changes?.ipfs_missing || null
    })));
  } catch (e) {
    res.status(500).json({ error: 'Failed to load alerts' });
  }
});

// GET /templates — list summaries
app.get('/templates', async (req, res) => {
  try {
    const { rows } = await pool.query(
      `SELECT t.template_id AS id, t.slug, t.title, t.locale, t.category, t.summary, t.default_currency,
              COUNT(m.*)::int AS milestones
         FROM templates t
         LEFT JOIN template_milestones m ON m.template_id = t.template_id
        GROUP BY t.template_id
        ORDER BY t.updated_at DESC, t.template_id DESC`
    );
    res.json(rows);
  } catch (e) {
    res.status(500).json({ error: 'failed_list_templates' });
  }
});

// GET /templates/:idOrSlug — detail with milestones
app.get('/templates/:idOrSlug', async (req, res) => {
  const raw = String(req.params.idOrSlug || '').trim();
  const isId = /^\d+$/.test(raw);
  try {
    const { rows: head } = await pool.query(
      `SELECT * FROM templates WHERE ${isId ? 'template_id' : 'slug'}=$1 LIMIT 1`,
      [isId ? Number(raw) : raw]
    );
    if (!head[0]) return res.status(404).json({ error: 'not_found' });

    const { rows: ms } = await pool.query(
      `SELECT idx, name, amount, days_offset, acceptance
         FROM template_milestones
        WHERE template_id=$1
        ORDER BY idx ASC`,
      [head[0].template_id]
    );
    res.json({ ...toCamel(head[0]), milestones: ms.map(toCamel) });
  } catch (e) {
    res.status(500).json({ error: 'failed_get_template' });
  }
});

// --- Admin Oversight: single payload for the dashboard ---
app.get('/admin/oversight', adminGuard, async (req, res) => {
  try {
    const out = {
      tiles: { openProofs: 0, breachingSla: 0, pendingPayouts: { count: 0, totalUSD: 0 }, escrowsLocked: 0, p50CycleHours: 0, revisionRatePct: 0 },
      queue: [], vendors: [], alerts: [], recent: [], payouts: { pending: [], recent: [] }
    };

    // tiles: open proofs & SLA
    {
      const { rows } = await pool.query(`
        SELECT
          COUNT(*) FILTER (WHERE status='pending') AS open_pending,
          COUNT(*) FILTER (WHERE status='pending' AND submitted_at < NOW() - INTERVAL '48 hours') AS breaching
        FROM proofs
        WHERE tenant_id = $1
      `, [req.tenantId]);
      out.tiles.openProofs = Number(rows[0].open_pending || 0);
      out.tiles.breachingSla = Number(rows[0].breaching || 0);
    }

    // tiles: pending payouts (ignore orphans)
    {
      const { rows } = await pool.query(`
    SELECT
      COUNT(*)::int                            AS count,
      COALESCE(SUM(mp.amount_usd), 0)::numeric AS total_usd
    FROM milestone_payments mp
    WHERE mp.status = 'pending' AND mp.tenant_id = $1
  `, [req.tenantId]).catch(() => ({ rows: [{ count: 0, total_usd: 0 }] }));

      out.tiles.pendingPayouts = {
        count: Number(rows[0].count || 0),
        totalUSD: Number(rows[0].total_usd || 0),
      };
    }

    // tiles: p50 approval cycle
    {
      const { rows } = await pool.query(`
        SELECT PERCENTILE_CONT(0.5) WITHIN GROUP (
                 ORDER BY EXTRACT(EPOCH FROM (COALESCE(approved_at, updated_at) - submitted_at))/3600.0
               ) AS p50h
        FROM proofs
        WHERE status='approved' AND submitted_at IS NOT NULL AND tenant_id = $1
      `, [req.tenantId]).catch(() => ({ rows: [{ p50h: 0 }] }));
      out.tiles.p50CycleHours = Number(rows[0].p50h || 0);
    }

    // tiles: revision rate
    {
      const { rows } = await pool.query(`
        SELECT
          COUNT(*) FILTER (WHERE status IN ('approved','rejected')) AS decided,
          COUNT(*) FILTER (WHERE status='rejected') AS rej
        FROM proofs
        WHERE tenant_id = $1
      `, [req.tenantId]).catch(() => ({ rows: [{ decided: 0, rej: 0 }] }));
      const decided = Number(rows[0].decided || 0);
      const rej = Number(rows[0].rej || 0);
      out.tiles.revisionRatePct = decided ? Math.round(100 * rej / decided) : 0;
    }

    // queue: oldest pending proofs
    {
      const { rows } = await pool.query(`
        SELECT p.proof_id, p.bid_id, p.milestone_index, p.status, p.submitted_at, p.updated_at,
               b.vendor_name, b.wallet_address, b.proposal_id, pr.title AS project
          FROM proofs p
          JOIN bids b       ON b.bid_id=p.bid_id
          JOIN proposals pr ON pr.proposal_id=b.proposal_id
         WHERE p.status='pending' AND p.tenant_id = $1
         ORDER BY p.submitted_at NULLS LAST, p.updated_at NULLS LAST
         LIMIT 50
      `, [req.tenantId]);
      out.queue = rows.map(r => ({
        id: r.proof_id,
        vendor: r.vendor_name || r.wallet_address,
        project: r.project,
        milestone: Number(r.milestone_index) + 1,
        ageHours: r.submitted_at ? Math.max(0, (Date.now() - new Date(r.submitted_at).getTime()) / 3600000) : null,
        status: r.status,
        risk: (r.submitted_at && (Date.now() - new Date(r.submitted_at).getTime()) > 48 * 3600000) ? 'sla' : null,
        actions: { bidId: r.bid_id, proposalId: r.proposal_id }
      }));
    }

    // vendors: performance
    {
      const { rows } = await pool.query(`
        SELECT
          b.vendor_name, b.wallet_address,
          COUNT(p.proof_id)                                   AS proofs,
          COUNT(p.proof_id) FILTER (WHERE p.status='approved') AS approved,
          COUNT(p.proof_id) FILTER (WHERE p.status='rejected') AS cr,
          COUNT(DISTINCT b.bid_id)                            AS bids,
          MAX(p.updated_at)                                   AS last_activity
        FROM bids b
        LEFT JOIN proofs p ON p.bid_id=b.bid_id
        WHERE b.tenant_id = $1
        GROUP BY b.vendor_name, b.wallet_address
        ORDER BY proofs DESC NULLS LAST, vendor_name ASC
        LIMIT 200
      `, [req.tenantId]);
      out.vendors = rows.map(r => ({
        vendor: r.vendor_name || '(unnamed)',
        wallet: r.wallet_address,
        proofs: Number(r.proofs || 0),
        approved: Number(r.approved || 0),
        cr: Number(r.cr || 0),
        approvalPct: Number(r.proofs || 0) ? Math.round(100 * Number(r.approved || 0) / Number(r.proofs || 0)) : 0,
        bids: Number(r.bids || 0),
        lastActivity: r.last_activity
      }));
    }

    // alerts: ipfs_missing from bid_audits
    {
      const { rows } = await pool.query(`
        SELECT ba.created_at, ba.bid_id, ba.changes
          FROM bid_audits ba
          JOIN bids b ON b.bid_id = ba.bid_id
         WHERE ba.changes ? 'ipfs_missing' AND b.tenant_id = $1
         ORDER BY ba.created_at DESC
         LIMIT 20
      `, [req.tenantId]);
      out.alerts = rows.map(r => ({
        type: 'ipfs_missing',
        createdAt: r.created_at,
        bidId: r.bid_id,
        details: r.changes?.ipfs_missing || null
      }));
    }

    // payouts (best-effort)
    {
      const { rows: pend } = await pool.query(`
        SELECT id, bid_id, milestone_index, amount_usd, created_at
          FROM milestone_payments
         WHERE status='pending' AND tenant_id = $1
         ORDER BY created_at DESC
         LIMIT 20
      `, [req.tenantId]).catch(() => ({ rows: [] }));
      const { rows: rec } = await pool.query(`
        SELECT id, bid_id, milestone_index, amount_usd, released_at
          FROM milestone_payments
         WHERE status='released' AND tenant_id = $1
         ORDER BY released_at DESC
         LIMIT 20
      `, [req.tenantId]).catch(() => ({ rows: [] }));
      out.payouts.pending = pend || [];
      out.payouts.recent = rec || [];
    }

    // recent activity = audits UNION released Safe payouts (so Safe shows up in Activity)
    {
      const { rows } = await pool.query(`
    SELECT *
    FROM (
      -- A) existing audit entries
      SELECT
        created_at,
        actor_role,
        actor_wallet,
        changes,
        bid_id

      FROM bid_audits ba
      JOIN bids b ON b.bid_id = ba.bid_id
      WHERE b.tenant_id = $1

      UNION ALL

      -- B) synthesized "payment_released" events for Safe payouts
      SELECT
        COALESCE(released_at, created_at) AS created_at,
        'system'::text                    AS actor_role,
        NULL::text                        AS actor_wallet,
        jsonb_build_object(
          'payment_released', jsonb_build_object(
            'milestone_index', milestone_index,
            'amount_usd',      amount_usd,
            'tx',              NULLIF(tx_hash, ''),
            'txHash',          NULLIF(tx_hash, ''),
            'via',             'safe',
            'safe_tx_hash',    NULLIF(safe_tx_hash, ''),
            'safeTxHash',      NULLIF(safe_tx_hash, '')
          )
        )                                  AS changes,
        bid_id
      FROM milestone_payments
      WHERE status = 'released' AND safe_tx_hash IS NOT NULL AND tenant_id = $1
    ) x
    ORDER BY created_at DESC
    LIMIT 200
  `).catch(() => ({ rows: [] }));
      out.recent = rows;
    }

    res.set('Cache-Control', 'no-store');
    res.json(out);
  } catch (e) {
    console.error('oversight error', e);
    res.status(500).json({ error: 'Failed to build oversight' });
  }
});

// (Place this below the GET /admin/oversight route in server.js)

app.post('/admin/oversight/reconcile-payouts', adminGuard, async (req, res) => {
  try {
    // 1. Fetch all pending payouts that have a transaction hash
    const { rows: pendingRows } = await pool.query(`
      SELECT id, bid_id, milestone_index, tx_hash
      FROM milestone_payments
      WHERE status = 'pending' AND tx_hash IS NOT NULL AND tenant_id = $1
    `, [req.tenantId]);

    if (pendingRows.length === 0) {
      return res.json({ ok: true, message: "No pending payouts to reconcile.", updated: 0 });
    }

    let updatedCount = 0;
    // 2. Check each pending payout's transaction on-chain
    for (const row of pendingRows) {
      const txHash = row.tx_hash;
      try {
        // Fetch the transaction receipt from the blockchain
        const receipt = await blockchainService.provider.getTransactionReceipt(txHash);
        if (receipt && receipt.confirmations >= 1 && receipt.status === 1) {
          // Transaction is confirmed and successful
          updatedCount++;
          // Mark this payout as released in the database
          await pool.query(`
  UPDATE milestone_payments
     SET status='released',
         released_at=NOW(),
         tx_hash = COALESCE(tx_hash, $2)
   WHERE id=$1 AND tenant_id=$3
`, [row.id, receipt.transactionHash, req.tenantId]);

          // (Optional: also update the related bid's milestone JSON to reflect released status)
          // You could load the bid and update its milestones[payload.milestone_index].paymentPending = false, etc.
        }
      } catch (err) {
        console.error(`Error checking receipt for tx ${txHash}:`, err);
        // If an error occurs (e.g., network issue), skip this one for now
      }
    }

    return res.json({ ok: true, updated: updatedCount });
  } catch (error) {
    console.error("Reconcile payouts failed:", error);
    return res.status(500).json({ error: "Internal error during reconciliation" });
  }
});

// Reconcile Safe multisig payments: flip 'pending' -> 'released' once executed on-chain
app.post('/admin/oversight/reconcile-safe', adminGuard, async (req, res) => {
  try {
    const { rows: pending } = await pool.query(`
      SELECT id, bid_id, milestone_index, amount_usd, safe_tx_hash
      FROM milestone_payments
      WHERE status='pending' AND safe_tx_hash IS NOT NULL AND tenant_id = $1
    `, [req.tenantId]);
    if (!pending.length) return res.json({ ok: true, updated: 0 });

    const { default: SafeApiKit } = await import('@safe-global/api-kit');
    const provider = new ethers.providers.JsonRpcProvider(process.env.SEPOLIA_RPC_URL);
    const net = await provider.getNetwork();
    const chainId = Number(net.chainId);
    const txServiceUrl = (process.env.SAFE_TXSERVICE_URL || 'https://safe-transaction-sepolia.safe.global')
      .trim()
      .replace(/\/+$/, '');

    const api = new SafeApiKit({
      chainId,
      txServiceUrl,
      apiKey: process.env.SAFE_API_KEY || undefined
    });

    let updated = 0;

    for (const row of pending) {
      if (!row.safe_tx_hash) continue;

      let txResp;
      try {
        txResp = await api.getTransaction(row.safe_tx_hash);
      } catch (e) {
        console.warn('[reconcile-safe] getTransaction failed', row.safe_tx_hash, e?.message || e);
        continue;
      }

      // must be executed on-chain (service provides transactionHash when executed)
      const executed = !!(txResp?.isExecuted && txResp?.transactionHash);
      if (!executed) continue;

      // --- Update bids.milestones (UI reads this) ---
      const { rows: bids } = await pool.query('SELECT * FROM bids WHERE bid_id=$1 AND tenant_id=$2', [row.bid_id, req.tenantId]);
      const bid = bids[0];
      if (!bid) continue;

      const milestones = Array.isArray(bid.milestones)
        ? bid.milestones
        : JSON.parse(bid.milestones || '[]');

      const idx = Number(row.milestone_index);
      const ms = { ...(milestones[idx] || {}) };
      const iso = new Date().toISOString();

      // ✅ set ALL paid markers the UI checks
      ms.paymentTxHash = ms.paymentTxHash || txResp.transactionHash;
      ms.safePaymentTxHash = ms.safePaymentTxHash || row.safe_tx_hash; // keep Safe ref
      ms.paymentDate = ms.paymentDate || iso;
      ms.paidAt = ms.paidAt || ms.paymentDate;
      ms.paymentPending = false;
      ms.status = 'paid';

      milestones[idx] = ms;

      await pool.query(
        'UPDATE bids SET milestones=$1 WHERE bid_id=$2 AND tenant_id=$3',
        [JSON.stringify(milestones), row.bid_id, req.tenantId]
      );

      // --- milestone_payments → released ---
      await pool.query(`
        UPDATE milestone_payments
           SET status='released',
               tx_hash=$2,
               released_at=NOW(),
               amount_usd=COALESCE(amount_usd,$3)
         WHERE id=$1 AND tenant_id=$4
      `, [row.id, txResp.transactionHash, row.amount_usd, req.tenantId]);

      // (optional) notify
      try {
        const { rows: [proposal] } = await pool.query(
          'SELECT * FROM proposals WHERE proposal_id=$1',
          [bid.proposal_id]
        );
        if (proposal && typeof notifyPaymentReleased === 'function') {
          await notifyPaymentReleased({
            bid,
            proposal,
            msIndex: idx + 1,
            amount: row.amount_usd,
            txHash: txResp.transactionHash
          });
        }
      } catch (e) {
        console.warn('[reconcile-safe] notify failed', e?.message || e);
      }

      // write an audit row so it appears under ACTIVITY
      try {
        await writeAudit(row.bid_id, req, {
          payment_released: {
            milestone_index: idx,
            amount_usd: row.amount_usd,
            tx: txResp.transactionHash,
            via: 'safe',
            safe_tx_hash: row.safe_tx_hash
          }
        });
      } catch (e) {
        console.warn('[reconcile-safe] audit failed', e?.message || e);
      }

      updated++;
    }

    return res.json({ ok: true, updated });
  } catch (e) {
    console.error('[reconcile-safe] fatal', e);
    return res.status(500).json({ error: e?.message || String(e) });
  }
});

// POST /admin/oversight/finalize-chain-tx  { bidId, milestoneIndex, txHash }
app.post('/admin/oversight/finalize-chain-tx', adminGuard, async (req, res) => {
  try {
    const bidId = Number(req.body?.bidId);
    const milestoneIndex = Number(req.body?.milestoneIndex);
    const txHash = String(req.body?.txHash || '').trim();

    if (!Number.isFinite(bidId) || !Number.isFinite(milestoneIndex) || !/^0x[0-9a-fA-F]{64}$/.test(txHash)) {
      return res.status(400).json({ error: 'bidId, milestoneIndex, txHash required' });
    }

    // 1) Verify on-chain receipt is successful
    const provider = new ethers.providers.JsonRpcProvider(process.env.SEPOLIA_RPC_URL);
    const receipt = await provider.getTransactionReceipt(txHash);
    if (!receipt || receipt.status !== 1) {
      return res.status(400).json({ error: 'tx not found or not successful on-chain' });
    }

    // 2) Load bid + milestones JSON
    const { rows: bids } = await pool.query('SELECT * FROM bids WHERE bid_id=$1 AND tenant_id=$2', [bidId, req.tenantId]);
    const bid = bids[0];
    if (!bid) return res.status(404).json({ error: 'Bid not found' });

    const milestones = Array.isArray(bid.milestones)
      ? bid.milestones
      : JSON.parse(bid.milestones || '[]');

    if (!milestones[milestoneIndex]) {
      return res.status(400).json({ error: 'Invalid milestoneIndex for this bid' });
    }

    // 3) Flip milestone -> PAID (preserve Safe refs if present)
    const ms = { ...(milestones[milestoneIndex] || {}) };
    const iso = new Date().toISOString();

    ms.paymentTxHash = ms.paymentTxHash || txHash;
    ms.paymentDate = ms.paymentDate || iso;
    ms.paidAt = ms.paidAt || ms.paymentDate;
    ms.paymentPending = false;
    ms.status = 'paid';

    milestones[milestoneIndex] = ms;

    await pool.query('UPDATE bids SET milestones=$1 WHERE bid_id=$2 AND tenant_id=$3', [JSON.stringify(milestones), bidId, req.tenantId]);

    // 4) Update or insert milestone_payments row as released
    const { rowCount } = await pool.query(
      `UPDATE milestone_payments
          SET status='released', tx_hash=$3, released_at=NOW()
        WHERE bid_id=$1 AND milestone_index=$2 AND tenant_id=$4`,
      [bidId, milestoneIndex, txHash, req.tenantId]
    );

    if (rowCount === 0) {
      await pool.query(
        `INSERT INTO milestone_payments
          (bid_id, milestone_index, created_at, tx_hash, status, released_at, tenant_id)
         VALUES ($1,$2,NOW(),$3,'released',NOW(),$4)`,
        [bidId, milestoneIndex, txHash, req.tenantId]
      );
    }

    // 5) Optional: notify
    try {
      const { rows: [proposal] } = await pool.query(
        'SELECT * FROM proposals WHERE proposal_id=$1',
        [bid.proposal_id]
      );
      if (proposal && typeof notifyPaymentReleased === 'function') {
        await notifyPaymentReleased({
          bid, proposal,
          msIndex: milestoneIndex + 1,
          amount: ms.amount || null,
          txHash
        });
      }
    } catch (e) {
      console.warn('notifyPaymentReleased failed', e?.message || e);
    }

    // >>> ADD THIS BLOCK (so Safe/Manual finalizations appear under ACTIVITY) <<<
    try {
      await writeAudit(bidId, req, {
        payment_released: {
          milestone_index: milestoneIndex,
          amount_usd: ms.amount || null,
          tx: txHash,
          via: 'manual_finalize'
        }
      });
    } catch (e) {
      console.warn('[finalize-chain-tx] audit failed', e?.message || e);
    }

    return res.json({ ok: true, bidId, milestoneIndex, txHash });
  } catch (e) {
    console.error('finalize-chain-tx failed', e);
    return res.status(500).json({ error: e?.message || String(e) });
  }
});

// Quick status check for a Safe tx
app.get('/safe/tx/:hash', adminGuard, async (req, res) => {
  try {
    const safeTxHash = String(req.params.hash);
    const { default: SafeApiKit } = await import('@safe-global/api-kit');

    // Prefer explicit chainId; default to Sepolia (11155111)
    const chainId = Number(process.env.SAFE_CHAIN_ID || 11155111);

    // Accept either the canonical tx-service domain or your custom one
    const txServiceUrl = (process.env.SAFE_TXSERVICE_URL || 'https://safe-transaction-sepolia.safe.global')
      .trim()
      .replace(/\/+$/, '');

    const api = new SafeApiKit({
      chainId,
      txServiceUrl,
      apiKey: process.env.SAFE_API_KEY || undefined,
    });

    const tx = await api.getTransaction(safeTxHash);

    return res.json({
      safeTxHash: tx.safeTxHash,
      isExecuted: !!tx.isExecuted,
      txHash: tx.transactionHash || null,
      confirmations: Array.isArray(tx.confirmations) ? tx.confirmations.length : 0,
    });
  } catch (err) {
    const msg = String(err?.message || err);

    // If the tx isn't known yet, treat as "not executed" so the client keeps polling
    if (/404|not\s*found/i.test(msg)) {
      return res.json({
        safeTxHash: req.params.hash,
        isExecuted: false,
        txHash: null,
        confirmations: 0,
      });
    }

    // Anything else is a server error
    return res.status(500).json({ error: msg });
  }
});

// Delete orphan milestone_payments rows (no matching bid)
app.post('/admin/oversight/payouts/prune-orphans', adminGuard, async (req, res) => {
  try {
    // Return what we’re going to delete (for visibility)
    const { rows: orphans } = await pool.query(`
      SELECT mp.id, mp.bid_id, mp.milestone_index, mp.amount_usd, mp.status, mp.created_at
      FROM milestone_payments mp
      WHERE NOT EXISTS (SELECT 1 FROM bids b WHERE b.bid_id = mp.bid_id)
        AND mp.tenant_id = $1
      ORDER BY mp.created_at DESC
    `, [req.tenantId]);

    if (orphans.length === 0) {
      return res.json({ ok: true, deleted: 0, orphans: [] });
    }

    // Delete them
    const { rows: deleted } = await pool.query(`
      DELETE FROM milestone_payments mp
      WHERE NOT EXISTS (SELECT 1 FROM bids b WHERE b.bid_id = mp.bid_id)
        AND mp.tenant_id = $1
      RETURNING mp.id, mp.bid_id, mp.milestone_index, mp.amount_usd, mp.status, mp.created_at
    `, [req.tenantId]);

    return res.json({ ok: true, deleted: deleted.length, orphans: deleted });
  } catch (e) {
    console.error('prune-orphans failed', e);
    return res.status(500).json({ ok: false, error: String(e?.message || e) });
  }
});

// --- IPFS monitor: scans recent CIDs and records "ipfs_missing" once ----------
const MONITOR_MINUTES = Number(process.env.IPFS_MONITOR_INTERVAL_MIN || 15);  // 0 = disabled
const MONITOR_LOOKBACK_DAYS = Number(process.env.IPFS_MONITOR_LOOKBACK_DAYS || 14);

async function runIpfsMonitor({ days = MONITOR_LOOKBACK_DAYS } = {}) {
  const started = Date.now();
  let checked = 0, flagged = 0;

  // 1) audit rows (the JSON you pin per audit)
  const { rows: auditRows } = await pool.query(`
    SELECT audit_id, bid_id, ipfs_cid
      FROM bid_audits
     WHERE ipfs_cid IS NOT NULL
       AND created_at >= NOW() - INTERVAL '${days} DAYS'
  `);

  for (const r of auditRows) {
    const cid = r.ipfs_cid;
    if (!cid) continue;
    checked++;

    // Two signals
    const alive = await checkCidAlive(cid);                   // gateway availability
    const missingOnPinata = await isMissingOnPinata(cid);     // Pinata pin state

    // If it's alive everywhere AND still pinned => nothing to do
    if (alive && !missingOnPinata) continue;

    // Already flagged for this cid?
    const { rows: exists } = await pool.query(
      `SELECT 1
         FROM bid_audits
        WHERE bid_id=$1
          AND changes ? 'ipfs_missing'
          AND changes->'ipfs_missing'->>'cid' = $2
        LIMIT 1`,
      [r.bid_id, cid]
    );
    if (exists.length) continue;

    // Choose a clear source for the finding
    const source = missingOnPinata
      ? (alive ? 'pinata_unpinned' : 'pinata_unpinned_and_dead')
      : 'gateway_dead';

    const payload = {
      ipfs_missing: {
        cid,
        source,
        seen: new Date().toISOString()
      }
    };

    const ins = await pool.query(
      `INSERT INTO bid_audits (bid_id, actor_role, actor_wallet, changes)
       VALUES ($1, 'system', NULL, $2)
       RETURNING audit_id`,
      [r.bid_id, payload]
    );
    if (typeof enrichAuditRow === 'function') enrichAuditRow(pool, ins.rows[0].audit_id, pinataUploadFile).catch(() => { });

    // Notify admins (best-effort)
    const [{ rows: bRows }, { rows: pRows }] = await Promise.all([
      pool.query('SELECT * FROM bids WHERE bid_id=$1', [r.bid_id]),
      pool.query('SELECT p.* FROM bids b JOIN proposals p ON p.proposal_id=b.proposal_id WHERE b.bid_id=$1', [r.bid_id])
    ]);
    await notifyIpfsMissing({ bid: bRows[0], proposal: pRows[0], cid, where: source });

    flagged++;
  }

  // 2) proof files (images/docs hosted on /ipfs/<cid>)
  const { rows: proofRows } = await pool.query(`
    SELECT proof_id, bid_id, files
      FROM proofs
     WHERE submitted_at >= NOW() - INTERVAL '${days} DAYS'
  `);

  for (const pr of proofRows) {
    const files = Array.isArray(pr.files) ? pr.files :
      (typeof pr.files === 'string' ? JSON.parse(pr.files || '[]') : []);
    for (const f of files) {
      const cid = extractCidFromUrl(f?.url);
      if (!cid) continue;
      checked++;

      const alive = await checkCidAlive(cid);
      const missingOnPinata = await isMissingOnPinata(cid);

      if (alive && !missingOnPinata) continue;

      const { rows: exists } = await pool.query(
        `SELECT 1
           FROM bid_audits
          WHERE bid_id=$1
            AND changes ? 'ipfs_missing'
            AND changes->'ipfs_missing'->>'cid' = $2
          LIMIT 1`,
        [pr.bid_id, cid]
      );
      if (exists.length) continue;

      const source = missingOnPinata
        ? (alive ? 'pinata_unpinned' : 'pinata_unpinned_and_dead')
        : 'gateway_dead';

      const payload = {
        ipfs_missing: {
          cid,
          source,
          proofId: pr.proof_id,
          url: f?.url || null,
          seen: new Date().toISOString()
        }
      };

      const ins = await pool.query(
        `INSERT INTO bid_audits (bid_id, actor_role, actor_wallet, changes)
         VALUES ($1, 'system', NULL, $2)
         RETURNING audit_id`,
        [pr.bid_id, payload]
      );
      if (typeof enrichAuditRow === 'function') enrichAuditRow(pool, ins.rows[0].audit_id, pinataUploadFile).catch(() => { });

      const [{ rows: bRows }, { rows: pRows }] = await Promise.all([
        pool.query('SELECT * FROM bids WHERE bid_id=$1', [pr.bid_id]),
        pool.query('SELECT p.* FROM bids b JOIN proposals p ON p.proposal_id=b.proposal_id WHERE b.bid_id=$1', [pr.bid_id])
      ]);
      await notifyIpfsMissing({
        bid: bRows[0],
        proposal: pRows[0],
        cid,
        where: source,
        proofId: pr.proof_id,
        url: f?.url || null
      });

      flagged++;
    }
  }

  console.log(`[ipfs-monitor] lookback=${days}d checked=${checked} flagged=${flagged} in ${Date.now() - started}ms`);
  return { checked, flagged, days };
}

// Manual trigger (useful for testing or external cron if you prefer)
app.get('/admin/ipfs/monitor-run', allowCron, async (req, res) => {
  try {
    const days = Math.max(1, Math.min(60, Number(req.query.days || MONITOR_LOOKBACK_DAYS)));
    const out = await runIpfsMonitor({ days });
    res.json({ ok: true, ...out });
  } catch (e) {
    res.status(500).json({ ok: false, error: String(e.message || e) });
  }
});

// Optional: auto-run every MONITOR_MINUTES (single global timer; no per-project cron)
if (MONITOR_MINUTES > 0) {
  setTimeout(() => runIpfsMonitor().catch(() => { }), 10_000); // first run ~10s after boot
  setInterval(() => runIpfsMonitor().catch(() => { }), MONITOR_MINUTES * 60 * 1000);
  console.log(`[ipfs-monitor] enabled: every ${MONITOR_MINUTES} min, lookback ${MONITOR_LOOKBACK_DAYS} days`);
} else {
  console.log('[ipfs-monitor] disabled (IPFS_MONITOR_INTERVAL_MIN=0)');
}

// --- Auto-reconcile Safe transactions (quiet + singleton) ---
const SAFE_RECONCILE_MINUTES = Number(process.env.SAFE_RECONCILE_MINUTES || 10);
const SAFE_RECONCILE_VERBOSE = (process.env.SAFE_RECONCILE_VERBOSE || '0') === '1';

let SAFE_RECONCILE_RUNNING = false;

async function autoReconcileSafeTransactionsOnce() {
  if (SAFE_RECONCILE_RUNNING) return;       // no overlaps
  SAFE_RECONCILE_RUNNING = true;

  try {
    // small batch each tick to avoid hammering
    const { rows: pendingTxs } = await pool.query(`
      SELECT id, bid_id, milestone_index, amount_usd, safe_tx_hash, tenant_id
      FROM milestone_payments
      WHERE status='pending' AND safe_tx_hash IS NOT NULL
      ORDER BY id DESC
      LIMIT 50
    `);

    if (!pendingTxs.length) {
      if (SAFE_RECONCILE_VERBOSE) console.log('[safe-reconcile] nothing pending');
      return;
    }

    if (SAFE_RECONCILE_VERBOSE) {
      console.log(`[safe-reconcile] pending batch: ${pendingTxs.length}`);
    }

    // Group pending txs by tenant to batch config fetching?
    // Or just fetch per row (simpler for now, 50 rows max)

    const { default: SafeApiKit } = await import('@safe-global/api-kit');

    let updated = 0;

    for (const row of pendingTxs) {
      try {
        // Fetch tenant config for this transaction
        const [tRpc, tService, tApiKey, tChainId] = await Promise.all([
          tenantService.getTenantConfig(row.tenant_id, 'safe_rpc_url'),
          tenantService.getTenantConfig(row.tenant_id, 'safe_service_url'),
          tenantService.getTenantConfig(row.tenant_id, 'safe_api_key'),
          tenantService.getTenantConfig(row.tenant_id, 'safe_chain_id')
        ]);

        const rpcUrl = tRpc || process.env.SEPOLIA_RPC_URL;
        const txServiceUrl = (tService || process.env.SAFE_TXSERVICE_URL || 'https://safe-transaction-sepolia.safe.global').trim().replace(/\/+$/, '');
        const apiKey = tApiKey || process.env.SAFE_API_KEY;
        const chainId = Number(tChainId || process.env.SAFE_CHAIN_ID || 11155111);

        if (!rpcUrl || !apiKey) continue; // Skip if not configured

        const api = new SafeApiKit({
          chainId,
          txServiceUrl,
          apiKey
        });

        const txResp = await api.getTransaction(row.safe_tx_hash);
        const executed = txResp?.isExecuted && txResp?.transactionHash;
        if (!executed) continue;

        // 1) finalize milestone_payments
        await pool.query(
          `UPDATE milestone_payments
             SET status='released', tx_hash=$2, released_at=NOW()
           WHERE id=$1 AND tenant_id=$3`,
          [row.id, txResp.transactionHash, row.tenant_id]
        );

        // 2) mark PAID on bids.milestones (the UI reads these)
        const { rows: bids } = await pool.query('SELECT milestones FROM bids WHERE bid_id=$1 AND tenant_id=$2', [row.bid_id, row.tenant_id]);
        if (!bids[0]) continue;

        const arr = Array.isArray(bids[0].milestones)
          ? bids[0].milestones
          : JSON.parse(bids[0].milestones || '[]');

        const idx = row.milestone_index;
        const ms = { ...(arr[idx] || {}) };
        const iso = new Date().toISOString();

        // set ALL paid markers your UI checks
        ms.paymentTxHash = ms.paymentTxHash || txResp.transactionHash;
        ms.safePaymentTxHash = ms.safePaymentTxHash || row.safe_tx_hash;
        ms.paymentDate = ms.paymentDate || iso;
        ms.paidAt = ms.paidAt || iso;
        ms.paymentPending = false;
        ms.status = 'paid';

        arr[idx] = ms;

        await pool.query('UPDATE bids SET milestones=$1 WHERE bid_id=$2 AND tenant_id=$3', [JSON.stringify(arr), row.bid_id, row.tenant_id]);

        // 3) (best-effort) notify
        try {
          const { rows: [proposal] } = await pool.query(
            'SELECT * FROM proposals WHERE proposal_id=(SELECT proposal_id FROM bids WHERE bid_id=$1)',
            [row.bid_id]
          );
          if (proposal && typeof notifyPaymentReleased === "function") {
            await notifyPaymentReleased({
              bid: { bid_id: row.bid_id }, // minimal payload is fine
              proposal,
              msIndex: row.milestone_index + 1,
              amount: row.amount_usd,
              txHash: txResp.transactionHash
            });
          }
        } catch (notifyErr) {
          if (SAFE_RECONCILE_VERBOSE) console.warn('Auto-reconcile notification failed', notifyErr);
        }

        updated++;
      } catch {
        // ignore and retry next tick
      }
    }

    if (updated > 0) {
      console.log(`[safe-reconcile] released ${updated} milestone(s)`);
    }
  } catch (e) {
    console.error('Auto-reconcile Safe transactions failed', e);
  } finally {
    SAFE_RECONCILE_RUNNING = false;
  }
}

// Start auto-reconciliation if enabled (guarded so we don't start twice)
if (SAFE_RECONCILE_MINUTES > 0) {
  if (!global.__SAFE_RECONCILER_STARTED__) {
    global.__SAFE_RECONCILER_STARTED__ = true;
    setTimeout(() => autoReconcileSafeTransactionsOnce().catch(() => { }), 30_000); // first run after 30s
    setInterval(
      () => autoReconcileSafeTransactionsOnce().catch(() => { }),
      SAFE_RECONCILE_MINUTES * 60 * 1000
    );
    console.log(`[safe-reconcile] enabled: every ${SAFE_RECONCILE_MINUTES} minutes`);
  }
} else {
  console.log('[safe-reconcile] disabled (SAFE_RECONCILE_MINUTES=0)');
}

// --- Bid Chat (SSE) ---------------------------------------------------------
app.all('/bids/:id/chat', (req, res, next) => {
  if (req.method === 'POST') return next();
  if (req.method === 'OPTIONS') {
    res.set('Allow', 'POST, OPTIONS');
    return res.sendStatus(204);
  }
  res.set('Allow', 'POST, OPTIONS');
  return res.status(405).json({ error: 'Method Not Allowed. Use POST /bids/:id/chat.' });
});

app.post('/bids/:id/chat', adminOrBidOwnerGuard, async (req, res) => {
  if (!openai) return res.status(503).json({ error: 'OpenAI not configured' });

  const bidId = Number(req.params.id);
  if (!Number.isFinite(bidId)) return res.status(400).json({ error: 'Invalid bid id' });

  const userMessages = Array.isArray(req.body?.messages) ? req.body.messages : [];

  // SSE headers
  res.set({
    'Content-Type': 'text/event-stream; charset=utf-8',
    'Cache-Control': 'no-cache, no-transform',
    'Connection': 'keep-alive',
  });
  if (typeof res.flushHeaders === 'function') res.flushHeaders();

  try {
    // Load bid + proposal
    const { rows: [bid] } = await pool.query('SELECT * FROM bids WHERE bid_id=$1', [bidId]);
    if (!bid) { res.write(`data: ERROR Bid not found\n\n`); res.write(`data: [DONE]\n\n`); return res.end(); }

    const { rows: [proposal] } = await pool.query('SELECT * FROM proposals WHERE proposal_id=$1', [bid.proposal_id]);
    if (!proposal) { res.write(`data: ERROR Proposal not found\n\n`); res.write(`data: [DONE]\n\n`); return res.end(); }

    // Load latest proofs for this bid
    const { rows: proofRows } = await pool.query(
      'SELECT * FROM proofs WHERE bid_id=$1 ORDER BY submitted_at DESC NULLS LAST LIMIT 5',
      [bidId]
    );

    const pinataJwt = await tenantService.getTenantConfig(req.tenantId, 'pinata_jwt');

    // ==================================================================
    // 1. Extract Text from the BID PDF (The Vendor's Offer)
    // ==================================================================
    let bidPdfText = "No bid PDF attached.";

    let bidRawFiles = Array.isArray(bid.files) ? bid.files : (bid.files ? JSON.parse(bid.files) : []);
    if (bid.doc) {
      const d = typeof bid.doc === 'string' ? JSON.parse(bid.doc) : bid.doc;
      if (d) bidRawFiles.push(d);
    }

    const bidPdfFile = bidRawFiles.find(f => {
      const n = (f.name || f.url || '').toLowerCase();
      return n.endsWith('.pdf') || n.includes('.pdf?') || (f.mimetype || '').includes('pdf');
    });

    if (bidPdfFile && bidPdfFile.url) {
      try {
        const cleanUrl = bidPdfFile.url.trim().replace(/[.,;]+$/, "");
        const info = await withTimeout(
          waitForPdfInfoFromDoc({ ...bidPdfFile, url: cleanUrl }, {}, pinataJwt), 8000, () => ({ used: false, reason: 'timeout' })
        );
        if (info.used && info.text) {
          bidPdfText = `BID PDF CONTENT (Truncated):\n"""\n${info.text.slice(0, 10000)}\n"""`;
        }
      } catch (e) { /* ignore */ }
    }

    // ==================================================================
    // 2. Extract Text from the PROPOSAL PDF (The Requirements)
    // ==================================================================
    let proposalPdfText = "No proposal PDF attached.";

    let propRawFiles = Array.isArray(proposal.docs) ? proposal.docs : (proposal.docs ? JSON.parse(proposal.docs) : []);

    const propPdfFile = propRawFiles.find(f => {
      const n = (f.name || f.url || '').toLowerCase();
      return n.endsWith('.pdf') || n.includes('.pdf?') || (f.mimetype || '').includes('pdf');
    });

    if (propPdfFile && propPdfFile.url) {
      try {
        const cleanUrl = propPdfFile.url.trim().replace(/[.,;]+$/, "");
        const info = await withTimeout(
          waitForPdfInfoFromDoc({ ...propPdfFile, url: cleanUrl }, {}, pinataJwt), 8000, () => ({ used: false, reason: 'timeout' })
        );
        if (info.used && info.text) {
          proposalPdfText = `PROPOSAL PDF CONTENT (Truncated):\n"""\n${info.text.slice(0, 10000)}\n"""`;
        }
      } catch (e) { /* ignore */ }
    }
    // ==================================================================

    // Normalize + (best-effort) PDF extraction for each proof
    const proofsCtx = [];
    for (const pr of proofRows) {
      const files = Array.isArray(pr.files)
        ? pr.files
        : (typeof pr.files === 'string' ? JSON.parse(pr.files || '[]') : []);
      const desc = String(pr.description || '').slice(0, 2000);
      const title = String(pr.title || `Proof for milestone ${Number(pr.milestone_index) + 1}`);

      // Try extract text from the first obvious PDF
      let pdfNote = 'No PDF detected.';
      const pdfFile = files.find(f => {
        const n = (f?.name || f?.url || '').toLowerCase();
        return n.endsWith('.pdf') || n.includes('.pdf?');
      });

      if (pdfFile && pdfFile.url) {
        try {
          const info = await withTimeout(
            waitForPdfInfoFromDoc({
              // 🛡️ FIX: Remove trailing dot/punctuation before downloading
              url: (pdfFile.url || "").trim().replace(/[.,;]+$/, ""),
              name: pdfFile.name || 'attachment.pdf',
              mimetype: 'application/pdf'
            }),
            8000,
            () => ({ used: false, reason: 'timeout' })
          );
          if (info.used) {
            const txt = (info.text || '').slice(0, 6000);
            pdfNote = `PDF EXTRACT (truncated): """${txt}"""`;
          } else {
            pdfNote = `No PDF text available (reason: ${info.reason || 'unknown'})`;
          }
        } catch (e) {
          pdfNote = `PDF extraction failed (${String(e).slice(0, 120)})`;
        }
      }

      const meta = Array.isArray(pr.file_meta)
        ? pr.file_meta
        : (typeof pr.file_meta === "string" ? JSON.parse(pr.file_meta || "[]") : []);
      const metaNote = summarizeMeta(meta);
      proofsCtx.push({
        milestoneIndex: pr.milestone_index,
        title,
        description: desc,
        files,
        pdfNote,
        metaNote,
      });
    }

    // Collect images from the latest proofs
    const imageFiles = [];
    for (const pr of proofRows) {
      const fs = Array.isArray(pr.files)
        ? pr.files
        : (typeof pr.files === 'string' ? JSON.parse(pr.files || '[]') : []);
      for (const f of fs) {
        if (isImageFile(f)) imageFiles.push(f);
      }
    }

    // Build chat context with **bid + proofs**
    const ai = coerceJson(bid.ai_analysis);
    const proofsBlock = proofsCtx.length
      ? proofsCtx.map((p, i) => {
        const filesList = (p.files || []).map(f => `- ${f.name || 'file'}: ${f.url}`).join('\n') || '(none)';
        return `
Proof #${i + 1} — Milestone ${Number(p.milestoneIndex) + 1}: ${p.title}
Description (truncated):
"""${p.description}"""
Files:
${filesList}

IMAGE/VIDEO METADATA:
${p.metaNote}

${p.pdfNote}`.trim();
      }).join('\n\n')
      : '(no proofs submitted for this bid)';

    const systemContext =
      `You are Agent2 for LithiumX.

--- PROPOSAL DETAILS ---
Org: ${proposal.org_name || ""}
Title: ${proposal.title || ""}
Summary: ${proposal.summary || ""}
Budget: $${proposal.amount_usd ?? 0}

--- PROPOSAL DOCUMENTS (Requirements) ---
${proposalPdfText}

--- BID DETAILS ---
Vendor: ${bid.vendor_name || ""}
Price: $${bid.price_usd ?? 0}
Timeline: ${bid.days ?? 0} days
Notes: ${bid.notes || ""}

--- BID DOCUMENTS (Offer) ---
${bidPdfText}

--- SUBMITTED PROOFS (Progress) ---
${proofsBlock}

Instruction:
- Compare the "BID DOCUMENTS" against the "PROPOSAL DOCUMENTS" to verify if the offer matches the requirements.
- Use the "SUBMITTED PROOFS" to verify actual progress.
- If the user asks about "the spec" or "requirements", check the Proposal PDF.
- If the user asks about "the offer" or "vendor plan", check the Bid PDF.
- Be concise.`;

    // One last user line to steer the answer
    const lastUserText =
      String(userMessages.at(-1)?.content || '').trim() ||
      'Analyze all provided materials, especially the images.';

    // BEFORE images from the proposal docs
    const proposalImages = collectProposalImages(proposal);

    // Decide vision vs. text (compare BEFORE vs AFTER when any images exist)
    let stream;
    if ((imageFiles.length > 0) || (proposalImages.length > 0)) {
      const systemMsg = `
You are Agent2 for LithiumX.
You CAN analyze the attached images.
Task: Compare "BEFORE" (proposal) vs "AFTER" (proof) images to assess progress/changes.
ALWAYS provide:
1) 1–2 sentence conclusion (done/partial/unclear).
2) Bullets with Evidence, Differences, Inconsistencies, OCR text, and Confidence [0–1].
Rules: Be concrete and cite visible cues.
`.trim();

      const userVisionContent = [
        { type: 'text', text: `User request: ${lastUserText}\n\nCompare BEFORE (proposal docs) vs AFTER (proofs) images.` },
      ];

      // ——— HELPER: Download & Convert to Base64 (Bypasses OpenAI Download Errors) ———
      const urlToContent = async (f) => {
        // 1. Filter non-images
        const name = (f.name || f.url || "").toLowerCase();
        const mime = (f.mimetype || "").toLowerCase();
        if (!mime.startsWith("image/") && !/\.(jpe?g|png|webp|gif)$/.test(name)) return null;

        try {
          // 2. Clean URL
          const url = (f.url || "").trim().replace(/[.,;]+$/, "");

          // 3. Download on YOUR server (Reliable)
          // We use your existing 'fetchAsBuffer' which handles retries/timeouts
          const buf = await fetchAsBuffer(url);

          // 4. Convert to Base64
          const b64 = buf.toString('base64');
          let finalMime = mime.startsWith("image/") ? mime : "image/jpeg"; // Fallback

          return { type: 'image_url', image_url: { url: `data:${finalMime};base64,${b64}` } };
        } catch (e) {
          console.warn(`[Vision] Skipped unreadable image ${f.url}:`, e.message);
          return null;
        }
      };
      // ——————————————————————————————————————————————————————————————————————————————

      // Process BEFORE Images (Limit to 3 to keep payload size manageable)
      const beforeProcessed = await Promise.all(proposalImages.slice(0, 3).map(urlToContent));
      const validBefore = beforeProcessed.filter(Boolean);

      if (validBefore.length > 0) {
        userVisionContent.push({ type: 'text', text: 'BEFORE (from proposal):' });
        userVisionContent.push(...validBefore);
      } else {
        userVisionContent.push({ type: 'text', text: 'BEFORE: (none or failed to load)' });
      }

      // Process AFTER Images (Limit to 3)
      const afterProcessed = await Promise.all(imageFiles.slice(0, 3).map(urlToContent));
      const validAfter = afterProcessed.filter(Boolean);

      if (validAfter.length > 0) {
        userVisionContent.push({ type: 'text', text: 'AFTER (from proofs):' });
        userVisionContent.push(...validAfter);
      } else {
        userVisionContent.push({ type: 'text', text: 'AFTER: (none or failed to load)' });
      }

      userVisionContent.push({ type: 'text', text: `\n\n--- CONTEXT ---\n${systemContext}` });

      console.log(`[Agent2] Sending Vision request with ${validBefore.length} before + ${validAfter.length} after images.`);

      stream = await openai.chat.completions.create({
        model: 'gpt-4o-mini',
        temperature: 0.2,
        stream: true,
        messages: [
          { role: 'system', content: systemMsg },
          { role: 'user', content: userVisionContent },
        ],
      });

    } else {
      // Text-only fallback
      const msgs = [
        { role: 'system', content: 'Be concise. If citing evidence, quote the exact line from the proof/PDF text.' },
        { role: 'user', content: `${lastUserText}\n\n--- CONTEXT ---\n${systemContext}` },
      ];
      stream = await openai.chat.completions.create({
        model: 'gpt-4o-mini',
        temperature: 0.2,
        messages: msgs,
        stream: true,
      });
    }

    // === SSE streaming loop (buffer + footer) ===
    let fullText = '';
    for await (const part of stream) {
      const token = part?.choices?.[0]?.delta?.content || '';
      if (token) {
        fullText += token;
        res.write(`data: ${token}\n\n`);
      }
    }

    // ---- Post-stream footer: confidence floor + Next checks ----
    const conf = extractConfidenceFromText(fullText);
    const hasAnyPdfText = proofsCtx.some(p => /^PDF EXTRACT/i.test(p.pdfNote || ''));
    const nextChecks = buildNextChecks({ hasAnyPdfText, imageCount: imageFiles.length });

    if (conf !== null && conf < 0.35) {
      res.write(`data: \n\n`);
      res.write(`data: 🔎 Needs human review (low confidence: ${conf.toFixed(2)})\n\n`);
    }

    if (nextChecks.length) {
      res.write(`data: \n\n`);
      res.write(`data: Next checks:\n\n`);
      for (const item of nextChecks) {
        res.write(`data: • ${item}\n\n`);
      }
    }

    res.write(`data: [DONE]\n\n`);
    res.end();
  } catch (err) {
    console.error('Bid chat SSE error:', err);
    try {
      res.write(`data: ERROR ${String(err).slice(0, 200)}\n\n`);
      res.write(`data: [DONE]\n\n`);
      res.end();
    } catch { }
  }
});

// --- Agent2 Chat about a PROOF (uses bid + proof + extracted PDF text) -----
app.post('/agent2/chat', adminGuard, async (req, res) => {
  try {
    const { bidId: rawBidId, proofId: rawProofId, message } = req.body || {};
    if (!message) return res.status(400).json({ error: 'Missing message' });

    // Load proof if provided (and derive bidId if needed)
    const proofId = Number(rawProofId);
    let proof = null;
    if (Number.isFinite(proofId)) {
      const { rows } = await pool.query('SELECT * FROM proofs WHERE proof_id=$1', [proofId]);
      proof = rows[0] || null;
    }

    let bidId = Number(rawBidId);
    if (!Number.isFinite(bidId) && proof) bidId = Number(proof.bid_id);

    if (!Number.isFinite(bidId)) {
      return res.status(400).json({ error: 'Provide bidId or a proofId that belongs to a bid' });
    }

    // Load bid + proposal for context
    const { rows: br } = await pool.query('SELECT * FROM bids WHERE bid_id=$1', [bidId]);
    const bid = br[0];
    if (!bid) return res.status(404).json({ error: 'Bid not found' });

    const { rows: pr } = await pool.query('SELECT * FROM proposals WHERE proposal_id=$1', [bid.proposal_id]);
    const proposal = pr[0] || null;

    // Collect proof text (description + any PDF text) — you likely already have this above; keep it once.
    const proofDesc = String(proof?.description || '').trim();
    let files = Array.isArray(proof?.files)
      ? proof.files
      : (typeof proof?.files === 'string' ? JSON.parse(proof.files || '[]') : []);

    // Build strict context
    const context = [
      'You are Agent 2 for LithiumX.',
      'Answer ONLY using the provided bid/proposal fields and the submitted proof (description + extracted PDF text).',
      'If something is not present in that material, say it is not stated in the submitted proof.',
      '',
      '--- PROPOSAL ---',
      JSON.stringify({
        org: proposal?.org_name || '',
        title: proposal?.title || '',
        summary: proposal?.summary || '',
        budgetUSD: proposal?.amount_usd ?? 0,
      }, null, 2),
      '',
      '--- BID ---',
      JSON.stringify({
        vendor: bid.vendor_name || '',
        priceUSD: bid.price_usd ?? 0,
        days: bid.days ?? 0,
        notes: bid.notes || '',
        milestones: (Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || '[]')),
      }, null, 2),
      '',
      '--- PROOF ---',
      JSON.stringify({
        title: proof?.title || '',
        description: proofDesc.slice(0, 4000),
        files: files.map(f => ({ name: f.name, url: f.url })),
      }, null, 2),
      '',
      '--- IMAGE/VIDEO METADATA ---',
      metaBlock,
      '',
      '--- KNOWN LOCATION ---',
      locationBlock,
      '',
      pdfText
        ? `--- PROOF PDF TEXT (truncated) ---\n${pdfText.slice(0, 15000)}`
        : `--- NO PDF TEXT AVAILABLE ---`,
    ].join('\n');

    if (!openai) return res.status(503).json({ error: 'OpenAI not configured' });

    const completion = await openai.chat.completions.create({
      model: 'gpt-4o-mini',
      temperature: 0.2,
      messages: [
        { role: 'system', content: 'Be concise. Cite precisely what is (or is not) in the proof.' },
        { role: 'user', content: `${message}\n\n--- CONTEXT ---\n${context}` },
      ],
    });

    const reply = completion.choices?.[0]?.message?.content?.trim() || 'No reply';
    res.json({ reply });
  } catch (err) {
    console.error('POST /agent2/chat error:', err);
    res.status(500).json({ error: 'Agent 2 failed to answer' });
  }
});

// 🔒 Guard: only allow POST/OPTIONS; block/log everything else
app.all('/bids/:id/analyze', (req, res, next) => {
  if (req.method === 'POST') return next();
  if (req.method === 'OPTIONS') {
    res.set('Allow', 'POST, OPTIONS');
    return res.sendStatus(204);
  }
  const ua = req.get('user-agent') || 'unknown';
  const ref = req.get('referer') || 'none';
  console.warn(`[UNEXPECTED ${req.method}] /bids/${req.params.id}/analyze  UA="${ua}"  Referer="${ref}"`);
  res.set('Allow', 'POST, OPTIONS');
  return res.status(405).json({ error: 'Method Not Allowed. Use POST /bids/:id/analyze.' });
});

app.post('/bids/:id/analyze', adminOrBidOwnerGuard, async (req, res) => {
  const bidId = Number(req.params.id);
  if (!Number.isFinite(bidId)) return res.status(400).json({ error: 'Invalid bid id' });

  try {
    // Fetch bid + proposal
    const { rows: [bid] } = await pool.query('SELECT * FROM bids WHERE bid_id=$1', [bidId]);
    if (!bid) return res.status(404).json({ error: 'Bid not found' });

    const { rows: [proposal] } = await pool.query(
      'SELECT * FROM proposals WHERE proposal_id=$1',
      [bid.proposal_id]
    );
    if (!proposal) return res.status(404).json({ error: 'Proposal not found' });

    const promptOverride = typeof req.body?.prompt === 'string' ? req.body.prompt : '';
    const analysis = await runAgent2OnBid(bid, proposal, { promptOverride, tenantId: req.tenantId });

    await pool.query('UPDATE bids SET ai_analysis=$1 WHERE bid_id=$2 AND tenant_id=$3', [
      JSON.stringify(analysis),
      bidId,
      req.tenantId
    ]);

    const { rows: updated } = await pool.query('SELECT * FROM bids WHERE bid_id=$1', [bidId]);
    return res.json(toCamel(updated[0]));
  } catch (err) {
    console.error('Analyze error:', err);
    return res.status(500).json({ error: 'Failed to analyze bid' });
  }
});

// ==============================
// Routes — Proofs
// ==============================
// server.js

app.get("/proofs", async (req, res) => {
  try {
    const bidId = Number(req.query.bidId);
    const proposalId = Number(req.query.proposalId);
    if (!Number.isFinite(bidId) && !Number.isFinite(proposalId)) {
      return res.status(400).json({ error: "Provide bidId or proposalId" });
    }

    // FIX: Added LEFT JOIN to milestone_payments (mp) to fetch payment status and tx_hash
    // We coalesce payment_tx_hash: prefer the one in milestone_payments, fallback to proof/bid logic if needed
    const selectSql = `
      SELECT
        p.*,
        mp.tx_hash AS payment_tx_hash,
        mp.safe_tx_hash AS safe_payment_tx_hash,
        mp.status AS payment_status,
        mp.released_at AS paid_at
      FROM proofs p
      LEFT JOIN milestone_payments mp
        ON mp.bid_id = p.bid_id
        AND mp.milestone_index = p.milestone_index
    `;

    let rows;
    if (Number.isFinite(bidId)) {
      ({ rows } = await pool.query(
        `${selectSql} WHERE p.bid_id = $1 AND p.tenant_id = $2 ORDER BY p.proof_id ASC`,
        [bidId, req.tenantId]
      ));
    } else {
      ({ rows } = await pool.query(
        `${selectSql}
         JOIN bids b ON b.bid_id = p.bid_id
         WHERE b.proposal_id = $1 AND b.tenant_id = $2
         ORDER BY p.proof_id ASC`,
        [proposalId, req.tenantId]
      ));
    }

    // normalize for the frontend
    const out = await Promise.all(rows.map(async r => {
      const o = toCamel(r);
      o.files = coerceJson(o.files) || [];
      o.fileMeta = coerceJson(o.fileMeta) || [];
      o.aiAnalysis = coerceJson(o.aiAnalysis) || null;
      o.geo = await buildSafeGeoForProof(o);

      // FIX: Explicitly set 'paid' flag if we found a hash or 'released' status
      if (o.paymentTxHash || o.paymentStatus === 'released') {
        o.paid = true;
        // Ensure tx hash is visible even if only found in mp table
        o.paymentTxHash = o.paymentTxHash || r.payment_tx_hash;
      }

      return o;
    }));

    res.json(out);
  } catch (e) {
    console.error("GET /proofs failed:", e);
    res.status(500).json({ error: "Failed to load proofs" });
  }
});

app.post("/proofs/:id/approve", adminGuard, async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid proof id" });

    const { rows: cur } = await pool.query(`SELECT * FROM proofs WHERE proof_id=$1 AND tenant_id=$2`, [id, req.tenantId]);
    const proof = cur[0];
    if (!proof) return res.status(404).json({ error: "Proof not found" });

    const { rows: upd } = await pool.query(
      `UPDATE proofs
          SET status='approved', approved_at=NOW(), updated_at=NOW()
        WHERE proof_id=$1 AND tenant_id=$2
      RETURNING *`,
      [id, req.tenantId]
    );
    const updated = upd[0];

    await writeAudit(Number(proof.bid_id), req, {
      proof_approved: { proofId: id, index: Number(proof.milestone_index) }
    });

    // notify
    const [{ rows: bRows }, { rows: pRows }] = await Promise.all([
      pool.query(`SELECT * FROM bids WHERE bid_id=$1`, [proof.bid_id]),
      pool.query(`SELECT * FROM proposals WHERE proposal_id=(SELECT proposal_id FROM bids WHERE bid_id=$1)`, [proof.bid_id])
    ]);
    if (typeof notifyProofApproved === "function") {
      const bid = bRows[0]; const proposal = pRows[0];
      const msIndex = Number(updated.milestone_index) + 1;
      notifyProofApproved({ proof: updated, bid, proposal, msIndex }).catch(() => { });
    }

    res.json(toCamel(updated));
  } catch (e) {
    console.error("POST /proofs/:id/approve failed:", e);
    res.status(500).json({ error: "Failed to approve proof" });
  }
});

app.post("/proofs/:id/reject", adminGuard, async (req, res) => {
  try {
    const id = Number(req.params.id);
    const reason = String(req.body?.reason || "").trim() || null;
    if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid proof id" });

    const { rows: cur } = await pool.query(`SELECT * FROM proofs WHERE proof_id=$1 AND tenant_id=$2`, [id, req.tenantId]);
    const proof = cur[0];
    if (!proof) return res.status(404).json({ error: "Proof not found" });

    const { rows: upd } = await pool.query(
      `UPDATE proofs
          SET status='rejected', updated_at=NOW()
        WHERE proof_id=$1 AND tenant_id=$2
      RETURNING *`,
      [id, req.tenantId]
    );

    await writeAudit(Number(proof.bid_id), req, {
      proof_rejected: { proofId: id, index: Number(proof.milestone_index), reason }
    });

    res.json(toCamel(upd[0]));
  } catch (e) {
    console.error("POST /proofs/:id/reject failed:", e);
    res.status(500).json({ error: "Failed to reject proof" });
  }
});

// Legacy complete route
app.put("/milestones/:bidId/:index/complete", async (req, res) => {
  try {
    const bidId = req.params.bidId;
    const idx = parseInt(req.params.index, 10);
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });

    const bid = rows[0];
    const milestones = Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || "[]");
    if (!milestones[idx]) return res.status(400).json({ error: "Invalid index" });

    milestones[idx].completed = true;
    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [JSON.stringify(milestones), bidId]);
    res.json({ success: true, milestones });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// ==============================
// Routes — Complete/Pay milestone (frontend-compatible)
// ==============================
app.post("/bids/:id/complete-milestone", adminOrBidOwnerGuard, async (req, res) => {
  const bidId = Number(req.params.id);
  const { milestoneIndex, proof } = req.body || {};
  if (!Number.isFinite(bidId)) return res.status(400).json({ error: "Invalid bid id" });
  if (!Number.isInteger(milestoneIndex) || milestoneIndex < 0) {
    return res.status(400).json({ error: "Invalid milestoneIndex" });
  }
  try {
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });

    const bid = rows[0];
    const milestones = Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || "[]");
    if (!milestones[milestoneIndex]) return res.status(400).json({ error: "Milestone index out of range" });

    const ms = milestones[milestoneIndex];
    ms.completed = true;
    ms.completionDate = new Date().toISOString();
    if (typeof proof === "string" && proof.trim()) ms.proof = proof.trim();

    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [JSON.stringify(milestones), bidId]);
    await writeAudit(bidId, req, {
      milestone_completed: { index: milestoneIndex, completionDate: ms.completionDate, proof: !!proof }
    });

    // --- BEGIN: approve latest proof for this milestone + notify ---
    if (NOTIFY_ENABLED) {
      try {
        // 1) Grab the latest proof for this (bid, milestone)
        const { rows: proofs } = await pool.query(
          `SELECT *
             FROM proofs
            WHERE bid_id = $1 AND milestone_index = $2
            ORDER BY proof_id DESC
            LIMIT 1`,
          [bidId, milestoneIndex]
        );
        const latest = proofs[0];

        // 2) If present and not already approved, flip to approved
        if (latest && String(latest.status || '').toLowerCase() !== 'approved') {
          const { rows: upd } = await pool.query(
            `UPDATE proofs
               SET status = 'approved', updated_at = NOW()
             WHERE proof_id = $1
             RETURNING *`,
            [latest.proof_id]
          );
          const updatedProof = upd[0];
          await writeAudit(bidId, req, { proof_approved: { index: milestoneIndex, proofId: updatedProof.proof_id } });

          // 3) Load proposal and fire the existing "proof approved" notifier
          const { rows: [proposal] } =
            await pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [bid.proposal_id]);

          if (proposal && typeof notifyProofApproved === "function") {
            console.log("[notify] approve about to send", {
              bidId,
              ms: milestoneIndex + 1,
              proofId: updatedProof.proof_id
            });
            await notifyProofApproved({
              proof: updatedProof,
              bid,
              proposal,
              msIndex: milestoneIndex + 1
            });
          }
        }
      } catch (e) {
        console.warn("notifyProofApproved via /complete-milestone failed:", String(e).slice(0, 200));
      }
    }
    // --- END: approve latest proof for this milestone + notify ---

    const { rows: updated } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
    return res.json(toCamel(updated[0]));
  } catch (err) {
    console.error("complete-milestone error", err);
    return res.status(500).json({ error: "Internal error completing milestone" });
  }
});

// ==============================
// Routes — Complete/Pay milestone (idempotent, fast-response)
// ==============================
app.post("/bids/:id/pay-milestone", adminGuard, async (req, res) => {
  const bidId = Number(req.params.id);
  const { milestoneIndex } = req.body || {};

  if (!Number.isFinite(bidId)) {
    return res.status(400).json({ error: "Invalid bid id" });
  }
  if (!Number.isInteger(milestoneIndex) || milestoneIndex < 0) {
    return res.status(400).json({ error: "Invalid milestoneIndex" });
  }

  try {
    // 0) Ensure the milestone_payments table/constraint exist (includes Safe columns)
    await pool.query(`
      CREATE TABLE IF NOT EXISTS milestone_payments (
        id              BIGSERIAL PRIMARY KEY,
        bid_id          BIGINT NOT NULL,
        milestone_index INT    NOT NULL,
        amount_usd      NUMERIC(18,2),
        status          TEXT CHECK (status IN ('pending','released')) DEFAULT 'pending',
        tx_hash         TEXT,
        safe_tx_hash    TEXT,
        safe_nonce      BIGINT,
        tenant_id       UUID REFERENCES tenants(id),
        created_at      TIMESTAMPTZ NOT NULL DEFAULT now(),
        released_at     TIMESTAMPTZ
      );
      ALTER TABLE milestone_payments
        ADD COLUMN IF NOT EXISTS amount_usd NUMERIC(18,2),
        ADD COLUMN IF NOT EXISTS status TEXT,
        ADD COLUMN IF NOT EXISTS tx_hash TEXT,
        ADD COLUMN IF NOT EXISTS safe_tx_hash TEXT,
        ADD COLUMN IF NOT EXISTS safe_nonce BIGINT,
        ADD COLUMN IF NOT EXISTS tenant_id UUID REFERENCES tenants(id),
        ADD COLUMN IF NOT EXISTS released_at TIMESTAMPTZ;
      DO $$
      BEGIN
        IF NOT EXISTS (
          SELECT 1 FROM pg_constraint WHERE conname = 'ux_milestone_payments_bid_ms'
        ) THEN
          ALTER TABLE milestone_payments
          ADD CONSTRAINT ux_milestone_payments_bid_ms UNIQUE (bid_id, milestone_index);
        END IF;
      END$$;
      ALTER TABLE milestone_payments ALTER COLUMN status SET DEFAULT 'pending';
    `);

    // 1) Load bid + milestone; bail if not ready
    const { rows: bids } = await pool.query("SELECT * FROM bids WHERE bid_id=$1 AND tenant_id=$2", [bidId, req.tenantId]);
    const bid = bids[0];
    if (!bid) return res.status(404).json({ error: "Bid not found" });

    const milestones = Array.isArray(bid.milestones)
      ? bid.milestones
      : JSON.parse(bid.milestones || "[]");

    if (!milestones[milestoneIndex]) {
      return res.status(400).json({ error: "Milestone index out of range" });
    }

    const ms = milestones[milestoneIndex];
    if (!ms.completed) {
      return res.status(400).json({ error: "Milestone not completed" });
    }

    // Legacy "already paid" signals
    if (ms.paymentTxHash || ms.paymentDate || ms.status === "paid") {
      return res.status(409).json({ error: "Milestone already paid" });
    }

    // 2) Idempotency gate (create PENDING row once)
    const msAmountUSD = Number(ms?.amount ?? 0);
    const ins = await pool.query(
      `INSERT INTO milestone_payments (bid_id, milestone_index, amount_usd, status, created_at, tenant_id)
       VALUES ($1, $2, $3, 'pending', NOW(), $4)
       ON CONFLICT (bid_id, milestone_index) DO NOTHING
       RETURNING id`,
      [bidId, milestoneIndex, msAmountUSD, req.tenantId]
    );

    if (ins.rowCount === 0) {
      const { rows: [existing] } = await pool.query(
        `SELECT status, tx_hash, safe_tx_hash FROM milestone_payments WHERE bid_id=$1 AND milestone_index=$2`,
        [bidId, milestoneIndex]
      );
      if (existing?.status === "released") {
        return res.status(409).json({ error: "Milestone already paid", txHash: existing.tx_hash || null });
      }
      return res.status(409).json({
        error: "Payment already in progress",
        txHash: existing?.tx_hash || existing?.safe_tx_hash || null
      });
    }

    // Mark payment as pending in the bid JSON immediately so the UI disables the Pay button
    try {
      ms.paymentPending = true;
      milestones[milestoneIndex] = ms;
      await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [JSON.stringify(milestones), bidId]);
    } catch (e) {
      console.warn("failed to mark paymentPending", e?.message || e);
    }

    // 3) Fire-and-forget transfer so the HTTP request returns fast
    setImmediate(async () => {
      try {
        // Decide if this payment will go via Safe (based on threshold + address)
        // Decide if this payment will go via Safe (based on threshold + address)
        const tThreshold = await tenantService.getTenantConfig(req.tenantId, 'safe_threshold_usd');
        const threshold = Number(tThreshold || 0);

        const willUseSafe =
          threshold > 0 &&
          msAmountUSD >= threshold;
        // Actually, we should check if we HAVE a safe address.
        // Re-check safe address existence inside the block or assume true if threshold met?
        // Let's keep existing logic but use the new threshold.

        // Notify admins that a milestone payment just entered "pending"
        try {
          const { rows: [proposal] } = await pool.query(
            "SELECT proposal_id, title, org_name FROM proposals WHERE proposal_id=$1",
            [bid.proposal_id]
          );
          if (proposal && typeof notifyPaymentPending === "function") {
            await notifyPaymentPending({
              bid,
              proposal,
              msIndex: milestoneIndex + 1,
              amount: msAmountUSD,
              method: willUseSafe ? "safe" : "direct",
              txRef: null
            });
          }
        } catch (e) {
          console.warn("notifyPaymentPending failed", e?.message || e);
        }

        // Preferred stablecoin symbol (e.g. USDT/USDC)
        const token = String(bid.preferred_stablecoin || "USDT").toUpperCase();

        // ---------- SAFE PATH (EIP-712; direct POST; sep base; checksummed addr; hard self-verify) ----------
        if (willUseSafe) {
          try {
            // FIX: Prefer tenant config for Safe settings
            const [tChainId, tRpc, tKey, tService, tApiKey, tThreshold, tSafeAddr] = await Promise.all([
              tenantService.getTenantConfig(req.tenantId, 'safe_chain_id'),
              tenantService.getTenantConfig(req.tenantId, 'safe_rpc_url'),
              tenantService.getTenantConfig(req.tenantId, 'safe_owner_key'),
              tenantService.getTenantConfig(req.tenantId, 'safe_service_url'),
              tenantService.getTenantConfig(req.tenantId, 'safe_api_key'),
              tenantService.getTenantConfig(req.tenantId, 'safe_threshold_usd'),
              tenantService.getTenantConfig(req.tenantId, 'safe_address')
            ]);

            const RPC_URL = tRpc;
            const SAFE_API_KEY = tApiKey;

            // FIX: Prefer tenant config for payment address (Safe Address)
            // Check safe_address first, then payment_address (legacy)
            const tenantPaymentAddress = await tenantService.getTenantConfig(req.tenantId, 'payment_address');
            const safeAddrRaw = tSafeAddr || tenantPaymentAddress || "";
            const SAFE_ADDRESS_CS = ethers.utils.getAddress(String(safeAddrRaw).trim()); // checksummed

            const TX_SERVICE_BASE = (tService || "https://api.safe.global/tx-service/sep")
              .trim()
              .replace(/\/+$/, "");

            if (!RPC_URL) throw new Error("RPC_URL not configured");
            if (!SAFE_API_KEY) throw new Error("SAFE_API_KEY not configured");
            if (!SAFE_ADDRESS_CS) throw new Error("SAFE_ADDRESS not configured");

            const provider = new ethers.providers.JsonRpcProvider(RPC_URL);

            // Minimal Safe ABI to read owners/nonce
            const SAFE_ABI = [
              "function getOwners() view returns (address[])",
              "function nonce() view returns (uint256)"
            ];
            const ZERO = "0x0000000000000000000000000000000000000000";
            const safeContract = new ethers.Contract(SAFE_ADDRESS_CS, SAFE_ABI, provider);

            // 1) pick a Safe owner key from env or tenant config
            const rawKeys = (tKey || process.env.SAFE_OWNER_KEYS || process.env.PRIVATE_KEYS || "")
              .split(",").map(s => s.trim()).filter(Boolean)
              .map(k => (k.startsWith("0x") ? k : `0x${k}`));
            if (!rawKeys.length) throw new Error("No SAFE_OWNER_KEYS/PRIVATE_KEYS configured");

            // 2) verify signer is an owner
            const ownersLc = (await safeContract.getOwners()).map(a => a.toLowerCase());
            console.log("[SAFE] owners (lc):", ownersLc);

            let signerWallet = null;
            for (const k of rawKeys) {
              const w = new ethers.Wallet(k, provider);
              if (ownersLc.includes(w.address.toLowerCase())) { signerWallet = w; break; }
            }
            if (!signerWallet) throw new Error(`None of the provided keys is a Safe owner. Owners: ${ownersLc.join(", ")}`);
            const senderAddr = await signerWallet.getAddress();
            console.log("[SAFE] using signer (owner):", senderAddr);

            // 3) resolve token + amount
            const tokenMeta = (TOKENS && TOKENS[token]) || {};
            const tokenAddr = tokenMeta.address;
            const tokenDec = Number.isInteger(tokenMeta.decimals) ? tokenMeta.decimals : 6;
            if (!tokenAddr) throw new Error(`Unknown token ${token} (no address in TOKENS)`);

            const amountUnits = typeof toTokenUnits === "function"
              ? await toTokenUnits(token, msAmountUSD)
              : ethers.utils.parseUnits(String(msAmountUSD), tokenDec);

            // 4) encode ERC20.transfer(to, amount)
            const erc20Iface = new ethers.utils.Interface(ERC20_ABI);
            const data = erc20Iface.encodeFunctionData("transfer", [bid.wallet_address, amountUnits]);
            if (typeof data !== "string" || !data.startsWith("0x")) throw new Error("[SAFE] invalid ERC20.transfer data");

            // 5) EIP-712 typed data (SafeTx)
            const chainId = Number(tChainId || process.env.SAFE_CHAIN_ID || 11155111); // Default Sepolia
            const op = 0; // CALL
            const nonceBn = await safeContract.nonce();
            const nonce = ethers.BigNumber.isBigNumber(nonceBn) ? nonceBn.toNumber() : Number(nonceBn);
            if (!Number.isFinite(nonce)) throw new Error("[SAFE] invalid Safe nonce");

            const domain = { chainId, verifyingContract: SAFE_ADDRESS_CS };
            const types = {
              SafeTx: [
                { name: "to", type: "address" },
                { name: "value", type: "uint256" },
                { name: "data", type: "bytes" },
                { name: "operation", type: "uint8" },
                { name: "safeTxGas", type: "uint256" },
                { name: "baseGas", type: "uint256" },
                { name: "gasPrice", type: "uint256" },
                { name: "gasToken", type: "address" },
                { name: "refundReceiver", type: "address" },
                { name: "nonce", type: "uint256" }
              ]
            };
            const value = {
              to: tokenAddr,
              value: "0",
              data,
              operation: op,
              safeTxGas: "0",
              baseGas: "0",
              gasPrice: "0",
              gasToken: ZERO,
              refundReceiver: ZERO,
              nonce: String(nonce)
            };

            // 6) sign typed data and SELF-VERIFY (EIP-712)
            const signatureRaw = await signerWallet._signTypedData(domain, types, value); // 65-byte sig
            const recovered = ethers.utils.verifyTypedData(domain, types, value, signatureRaw);
            if (recovered.toLowerCase() !== senderAddr.toLowerCase()) {
              throw new Error(`[SAFE] EIP-712 signature mismatch BEFORE POST: recovered ${recovered}, expected ${senderAddr}`);
            }

            // 7) compute the contractTransactionHash (REQUIRED by Tx-Service)
            const contractTransactionHash = ethers.utils._TypedDataEncoder.hash(domain, types, value);

            // Tx-Service expects EIP-712 signatures with type suffix "02"
            const hexNoPrefix = signatureRaw.slice(2);
            if (hexNoPrefix.length !== 130) {
              throw new Error(`[SAFE] unexpected EIP-712 signature length=${hexNoPrefix.length} (expected 130)`);
            }
            const senderSignature = signatureRaw + "02";

            // 8) DIRECT POST to Safe Tx-Service (checksummed address; 'sep' base)
            console.log("[SAFE] using DIRECT POST path");
            console.log("[SAFE] POST", `${TX_SERVICE_BASE}/api/v2/safes/${SAFE_ADDRESS_CS}/multisig-transactions/`);

            // optional: early info check for clearer error
            {
              const info = await fetch(`${TX_SERVICE_BASE}/api/v1/safes/${SAFE_ADDRESS_CS}/`, {
                headers: { "Authorization": `Bearer ${SAFE_API_KEY}` }
              });
              if (!info.ok) {
                const msg = await info.text().catch(() => "");
                throw new Error(`[SAFE info] ${info.status} ${msg || info.statusText}`);
              }
            }

            const body = {
              to: tokenAddr,
              value: "0",
              data,
              operation: 0,
              gasToken: ZERO,
              safeTxGas: 0,
              baseGas: 0,
              gasPrice: "0",
              refundReceiver: ZERO,
              nonce,
              contractTransactionHash,          // <-- REQUIRED (this fixes the 422)
              sender: senderAddr,
              signature: senderSignature,       // EIP-712 + "02"
              origin: "milestone-pay"
            };

            const resp = await fetch(`${TX_SERVICE_BASE}/api/v2/safes/${SAFE_ADDRESS_CS}/multisig-transactions/`, {
              method: "POST",
              headers: {
                "content-type": "application/json",
                "Authorization": `Bearer ${SAFE_API_KEY}`
              },
              body: JSON.stringify(body)
            });

            if (!resp.ok) {
              const txt = await resp.text().catch(() => "");
              throw new Error(`TxService propose failed [${resp.status}] ${txt || resp.statusText}`);
            }

            // 9) store the tx hash + nonce (use the typed-data hash)
            await pool.query(
              `UPDATE milestone_payments
     SET safe_tx_hash=$3, safe_nonce=$4
   WHERE bid_id=$1 AND milestone_index=$2`,
              [bidId, milestoneIndex, contractTransactionHash, nonce]
            );

            // === A) Write in-flight markers into bids.milestones so UI hides buttons & can poll ===
            try {
              const { rows } = await pool.query(
                'SELECT milestones FROM bids WHERE bid_id=$1 LIMIT 1',
                [bidId]
              );
              const milestonesJson = rows?.[0]?.milestones;
              const milestonesArr = Array.isArray(milestonesJson)
                ? milestonesJson
                : JSON.parse(milestonesJson || '[]');

              const ms = { ...(milestonesArr[milestoneIndex] || {}) };

              // Markers the UI looks for to treat as "in-flight"
              ms.safePaymentTxHash = contractTransactionHash;      // Client polls /safe/tx/:hash with this
              ms.safeTxHash = ms.safeTxHash || contractTransactionHash;
              ms.safeNonce = nonce;
              ms.safeStatus = 'submitted';
              ms.paymentPending = true;
              if (!ms.status || ms.status === 'approved') ms.status = 'pending';

              milestonesArr[milestoneIndex] = ms;

              await pool.query(
                'UPDATE bids SET milestones=$1 WHERE bid_id=$2',
                [JSON.stringify(milestonesArr), bidId]
              );
            } catch (e) {
              console.warn('Failed to persist in-flight markers to milestones JSON', e?.message || e);
            }

            // === B) Immediate executed check: if already executed -> mark as PAID now ===
            {
              // Use rate-limited fetch if available; otherwise fall back to fetch
              const _safeFetch = (typeof safeFetchRL === 'function') ? safeFetchRL : fetch;

              try {
                const url = `${TX_SERVICE_BASE}/api/v1/multisig-transactions/${contractTransactionHash}`;
                const r = await _safeFetch(url);

                if (r.ok) {
                  const t = await r.json().catch(() => null);

                  // Robust execution detection across Safe API variants
                  const statusStr = String(t?.tx_status || t?.status || "").toLowerCase();
                  const executed =
                    !!t?.is_executed ||
                    !!t?.isExecuted ||
                    !!t?.execution_date ||
                    !!t?.executionDate ||
                    !!t?.transaction_hash ||
                    !!t?.transactionHash ||
                    statusStr === "success" ||
                    statusStr === "executed" ||
                    statusStr === "successful";

                  if (executed) {
                    const finalTxHash =
                      t?.transaction_hash || t?.transactionHash || t?.tx_hash || t?.txHash || contractTransactionHash;

                    // milestone_payments → mark released now
                    await pool.query(
                      `UPDATE milestone_payments
             SET status='released', tx_hash=$3, released_at=NOW()
           WHERE bid_id=$1 AND milestone_index=$2`,
                      [bidId, milestoneIndex, finalTxHash]
                    );

                    // bids.milestones → fields the FE's isPaid() relies on
                    const iso = new Date().toISOString();
                    await upsertMilestoneFields(bidId, milestoneIndex, {
                      paymentTxHash: finalTxHash,
                      paymentDate: iso,
                      paidAt: iso,
                      paid: true,
                      status: 'paid',
                      paymentPending: false,
                    });

                    // best-effort notify (ignore failures)
                    if (proposal && typeof notifyPaymentReleased === 'function') {
                      try {
                        await notifyPaymentReleased({
                          bid,
                          proposal,
                          msIndex: milestoneIndex + 1,
                          amount: msAmountUSD,
                          txHash: finalTxHash,
                        });
                      } catch { }
                    }

                    return res.json({ ok: true, status: 'released', txHash: finalTxHash });
                  }
                  // Not executed yet → fall through to pending below
                } else {
                  const txt = await r.text().catch(() => '');
                  console.warn('Immediate Safe check HTTP failed', r.status, txt || r.statusText);
                  // fall through to pending
                }
              } catch (e) {
                console.warn('Immediate Safe execution check failed, proceeding with pending', e?.message || e);
                // fall through to pending
              }
            }

            // 10) notify
            try {
              const { rows: [proposal] } = await pool.query(
                "SELECT proposal_id, title, org_name FROM proposals WHERE proposal_id=$1",
                [bid.proposal_id]
              );
              if (proposal && typeof notifyPaymentPending === "function") {
                await notifyPaymentPending({
                  bid,
                  proposal,
                  msIndex: milestoneIndex + 1,
                  amount: msAmountUSD,
                  method: "safe",
                  txRef: contractTransactionHash
                });
              }
            } catch (e) {
              console.warn("notifyPaymentPending (post-safe-hash) failed", e?.message || e);
            }

            return;
          } catch (safeErr) {
            console.error("SAFE propose failed; leaving pending", safeErr?.message || safeErr);
            return;
          }
        }

        // ---------- MANUAL/EOA PATH ----------
        let txHash;
        if (blockchainService?.transferSubmit) {
          const r = await blockchainService.transferSubmit(token, bid.wallet_address, msAmountUSD);
          txHash = r?.hash;
        } else if (blockchainService?.sendToken) {
          const r = await blockchainService.sendToken(token, bid.wallet_address, msAmountUSD, bid.tenant_id);
          txHash = r?.hash;
        } else {
          txHash = "dev_" + crypto.randomBytes(8).toString("hex");
        }

        // --- FALLBACK: recover tx hash from chain logs if wrapper returned none ---
        if (!txHash) {
          const rpcUrl =
            process.env.PAYOUT_RPC_URL ||
            process.env.ANCHOR_RPC_URL ||
            process.env.SEPOLIA_RPC_URL; // make sure this matches the CHAIN you paid on
          const tokenKeyOrAddr = (TOKENS[token]?.address) ? TOKENS[token].address : token; // "USDT" -> TOKENS.USDT.address, or 0x...
          try {
            const recovered = await salvageTxHashViaLogs(
              rpcUrl,
              tokenKeyOrAddr,
              bid.wallet_address,
              msAmountUSD
            );
            if (recovered) {
              txHash = recovered;
              console.log('[SALVAGE] recovered txHash:', txHash);
            }
          } catch (e) {
            console.warn('[SALVAGE] error:', e?.message || e);
          }
        }

        if (txHash) {
          await pool.query(
            `UPDATE milestone_payments SET tx_hash=$3 WHERE bid_id=$1 AND milestone_index=$2`,
            [bidId, milestoneIndex, txHash]
          );
        }

        // Optional confirm (1 conf). MUST NOT block the HTTP response.
        try {
          if (blockchainService?.waitForConfirm && txHash && !txHash.startsWith("dev_")) {
            await blockchainService.waitForConfirm(txHash, 1);
          }
        } catch (e) {
          console.warn("waitForConfirm failed (left as pending)", e?.message || e);
          return;
        }

        // 4) Mark released + legacy JSON fields
        ms.paymentTxHash = txHash || ms.paymentTxHash || null;
        ms.paymentDate = new Date().toISOString();
        ms.paymentPending = false;
        ms.status = "paid";
        milestones[milestoneIndex] = ms;

        await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [JSON.stringify(milestones), bidId]);
        await pool.query(
          `UPDATE milestone_payments
     SET status='released', tx_hash=COALESCE(tx_hash,$3), released_at=NOW(), amount_usd=COALESCE(amount_usd,$4)
   WHERE bid_id=$1 AND milestone_index=$2`,
          [bidId, milestoneIndex, txHash || null, msAmountUSD]
        );

        // 5) Notify best-effort
        try {
          const { rows: [proposal] } = await pool.query(
            "SELECT * FROM proposals WHERE proposal_id=$1",
            [bid.proposal_id]
          );
          if (proposal && typeof notifyPaymentReleased === "function") {
            await notifyPaymentReleased({
              bid, proposal,
              msIndex: milestoneIndex + 1,
              amount: msAmountUSD,
              txHash: txHash || null
            });
          }
        } catch (e) {
          console.warn("notifyPaymentReleased failed", e?.message || e);
        }

        // Optional: audit
        try {
          await writeAudit(bidId, req, {
            payment_released: {
              milestone_index: milestoneIndex,
              amount_usd: msAmountUSD,
              tx: txHash || null
            }
          });
        } catch { }
      } catch (e) {
        console.error("Background pay-milestone failed (left pending)", e);
      }
    });

    // 5) Return immediately to avoid proxy 502s on slow confirmations
    return res.status(202).json({
      ok: true,
      status: "pending",
      bidId,
      milestoneIndex,
    });

  } catch (err) {
    console.error("pay-milestone error", err);
    const msg = err?.shortMessage || err?.reason || err?.message || "Internal error paying milestone";
    return res.status(500).json({ ok: false, error: msg });
  }
});

// ==============================
//  — Proofs (robust, with Agent2)
// ==============================
app.post("/proofs", authRequired, async (req, res) => {
  // Accept legacy & new shapes
  const schema = Joi.object({
    bidId: Joi.number().integer().required(),
    milestoneIndex: Joi.number().integer().min(0).required(),
    // legacy:
    proof: Joi.string().allow("").optional(),
    // new:
    title: Joi.string().allow("").optional(),
    description: Joi.string().allow("").optional(),
    files: Joi.array()
      .items(Joi.object({ name: Joi.string().allow(""), url: Joi.string().uri().required() }))
      .default([])
      .optional(),
    prompt: Joi.string().allow("").optional(),
    vendorPrompt: Joi.string().allow("").optional(),
  }).or("proof", "description").messages({
    "object.missing": "Must provide either proof (legacy) or description (new format)",
  });

  const { error, value } = schema.validate(req.body || {}, { abortEarly: false });
  if (error) return res.status(400).json({ error: error.message });

  const { bidId, milestoneIndex } = value;

  try {
    // 1) Ensure bid exists & caller allowed
    const { rows: bids } = await pool.query("SELECT * FROM bids WHERE bid_id=$1 AND tenant_id=$2", [bidId, req.tenantId]);
    if (!bids[0]) return res.status(404).json({ error: "Bid not found" });
    const bid = bids[0];

    const caller = String(req.user?.sub || "").toLowerCase();
    const isAdmin = String(req.user?.role || "").toLowerCase() === "admin";
    if (!isAdmin && caller !== String(bid.wallet_address || "").toLowerCase()) {
      return res.status(403).json({ error: "Forbidden" });
    }

    // 2) Validate milestone
    const milestones = Array.isArray(bid.milestones)
      ? bid.milestones
      : JSON.parse(bid.milestones || "[]");
    if (!milestones[milestoneIndex]) {
      return res.status(400).json({ error: "Invalid milestoneIndex for this bid" });
    }

    // 3) Duplicate guards
    const { rows: pend } = await pool.query(
      `SELECT 1 FROM proofs WHERE bid_id=$1 AND milestone_index=$2 AND status='pending' AND tenant_id=$3 LIMIT 1`,
      [bidId, milestoneIndex, req.tenantId]
    );
    if (pend.length) {
      return res.status(409).json({ error: "A proof is already pending review for this milestone." });
    }
    const { rows: lastRows } = await pool.query(
      `SELECT status
         FROM proofs
        WHERE bid_id=$1 AND milestone_index=$2 AND tenant_id=$3
        ORDER BY submitted_at DESC NULLS LAST,
                 updated_at  DESC NULLS LAST,
                 proof_id    DESC
        LIMIT 1`,
      [bidId, milestoneIndex, req.tenantId]
    );
    if (lastRows[0] && String(lastRows[0].status || "").toLowerCase() === "approved") {
      return res.status(409).json({ error: "This milestone has already been approved." });
    }

    // 4) Normalize proof fields
    const files = Array.isArray(value.files) ? value.files : [];
    const mediaFiles = files.filter(isMediaFile);
    const fileMeta = await Promise.all(mediaFiles.map(extractFileMetaFromUrl)).then(a => a.filter(Boolean));

    // helpers
    function findFirstGps(arr = []) {
      for (const m of arr) {
        const lat = Number(m?.exif?.gpsLatitude);
        const lon = Number(m?.exif?.gpsLongitude);
        if (Number.isFinite(lat) && Number.isFinite(lon)) {
          const alt = Number.isFinite(Number(m?.exif?.gpsAltitude)) ? Number(m?.exif?.gpsAltitude) : null;
          return { lat, lon, alt };
        }
      }
      return { lat: null, lon: null, alt: null };
    }
    function findFirstCaptureIso(arr = []) {
      for (const m of arr) {
        const raw = m?.exif?.createDate;
        if (!raw) continue;
        const norm = String(raw).replace(/^([0-9]{4}):([0-9]{2}):([0-9]{2})\s/, "$1-$2-$3 ");
        const d = new Date(norm + "Z");
        if (!Number.isNaN(d.getTime())) return d.toISOString();
      }
      return null;
    }

    const { lat: gpsLat, lon: gpsLon, alt: gpsAlt } = findFirstGps(fileMeta);
    const captureIso = findFirstCaptureIso(fileMeta);
    // Reverse geocode once if we have GPS
    let rgeo = null;
    if (Number.isFinite(gpsLat) && Number.isFinite(gpsLon)) {
      try { rgeo = await reverseGeocode(gpsLat, gpsLon); } catch { }
    }

    const legacyText = (value.proof || "").trim();
    const description = (value.description || legacyText || "").trim();
    const title = (value.title || `Proof for Milestone ${milestoneIndex + 1}`).trim();
    const vendorPrompt = (value.vendorPrompt || value.prompt || "").trim();

    // 5) Insert proof row
    const insertQ = `
      INSERT INTO proofs
        (bid_id, milestone_index, vendor_name, wallet_address, title, description,
         files, file_meta, gps_lat, gps_lon, gps_alt, capture_time,
         status, submitted_at, vendor_prompt, updated_at, tenant_id)
       VALUES
         ($1,$2,$3,$4,$5,$6,
          $7,$8,$9,$10,$11,$12,
          'pending', NOW(), $13, NOW(), $14)
       RETURNING *`;
    const insertVals = [
      bidId,
      milestoneIndex,
      bid.vendor_name || bid.vendorName || null,
      bid.wallet_address || bid.walletAddress || null,
      title,
      description,
      JSON.stringify(files),
      JSON.stringify(fileMeta || []),
      gpsLat, gpsLon, gpsAlt, captureIso,
      vendorPrompt || "",
      req.tenantId
    ];
    const { rows: pr } = await pool.query(insertQ, insertVals);
    let proofRow = pr[0];
    await writeAudit(bidId, req, {
      proof_submitted: {
        index: milestoneIndex,
        proofId: proofRow.proof_id,
        files: files,
        hasGps: Number.isFinite(gpsLat) && Number.isFinite(gpsLon)
      }
    });


    // 6) (Best-effort) Agent2 analysis + notify
    try {
      if (openai && (vendorPrompt || description || files.length)) {
        const { rows: prj } = await pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [
          bid.proposal_id || bid.proposalId,
        ]);
        const proposal = prj[0] || null;

        const metaBlock = summarizeMeta(fileMeta);
        const gpsCount = fileMeta.filter(m =>
          Number.isFinite(m?.exif?.gpsLatitude) && Number.isFinite(m?.exif?.gpsLongitude)
        ).length;
        const firstFix = fileMeta.find(m =>
          Number.isFinite(m?.exif?.gpsLatitude) && Number.isFinite(m?.exif?.gpsLongitude)
        );
        const firstGps = firstFix
          ? {
            lat: Number(firstFix.exif.gpsLatitude),
            lon: Number(firstFix.exif.gpsLongitude),
            alt: Number.isFinite(Number(firstFix?.exif?.gpsAltitude))
              ? Number(firstFix.exif.gpsAltitude)
              : null,
          }
          : { lat: null, lon: null, alt: null };

        const capNote = captureIso ? `First capture time (EXIF, ISO8601): ${captureIso}` : "No capture time in EXIF.";
        const gpsNote = gpsCount
          ? `GPS present in ${gpsCount} file(s). First fix: ${firstGps.lat}, ${firstGps.lon}${firstGps.alt != null ? ` • alt ${firstGps.alt}m` : ""}`
          : "No GPS in submitted media.";

        const basePrompt = `
You are Agent2. Evaluate a vendor's submitted proof for a specific milestone.

Return strict JSON:
{
  "summary": string,
  "evidence": string[],
  "gaps": string[],
  "fit": "low" | "medium" | "high",
  "confidence": number,
  "geo": {
    "gpsCount": number,
    "firstFix": { "lat": number|null, "lon": number|null, "alt": number|null },
    "captureTime": string|null
  }
}

Context:
- Proposal: ${proposal?.title || "(unknown)"} (${proposal?.org_name || "(unknown)"})
- Milestone: ${milestones[milestoneIndex]?.name || "(unknown)"} — $${milestones[milestoneIndex]?.amount ?? "?"}
- Vendor: ${bid.vendor_name || bid.vendorName || "(unknown)"}

Proof title: ${title}
Proof description (truncated):
"""${description.slice(0, 2000)}"""

Files:
${files.map((f) => `- ${f.name || "file"}: ${f.url}`).join("\n") || "(none)"}

MEDIA METADATA (EXIF/GPS summary):
${metaBlock}

Hints:
- ${gpsNote}
- ${capNote}
`.trim();

        const fullPrompt = vendorPrompt ? `${vendorPrompt}\n\n---\n${basePrompt}` : basePrompt;

        const resp = await openai.chat.completions.create({
          model: "gpt-4o-mini",
          temperature: 0.2,
          messages: [{ role: "user", content: fullPrompt }],
          response_format: { type: "json_object" },
        });

        let analysis;
        try {
          const raw = resp.choices?.[0]?.message?.content || "{}";
          analysis = JSON.parse(raw);
        } catch {
          analysis = { summary: "Agent2 returned non-JSON.", evidence: [], gaps: [], fit: "low", confidence: 0 };
        }
        if (!analysis.geo) {
          analysis.geo = { gpsCount, firstFix: firstGps, captureTime: captureIso || null };
        }

        await pool.query(
          "UPDATE proofs SET ai_analysis=$1, updated_at=NOW() WHERE proof_id=$2",
          [JSON.stringify(analysis), proofRow.proof_id]
        );
        proofRow.ai_analysis = analysis;
        await writeAudit(bidId, req, {
          proof_analyzed: {
            index: milestoneIndex,
            proofId: proofRow.proof_id,
            fit: analysis?.fit,
            confidence: analysis?.confidence
          }
        });

        // notify if suspicious
        if (shouldNotify(analysis)) {
          try {
            const { rows: prj2 } = await pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [
              bid.proposal_id || bid.proposalId,
            ]);
            const proposal2 = prj2[0] || null;
            await notifyProofFlag({ proof: proofRow, bid, proposal: proposal2, analysis });
          } catch (e) {
            console.warn("notifyProofFlag failed (non-fatal):", String(e).slice(0, 200));
          }
        }
      }
    } catch (e) {
      console.warn("Agent2 analysis skipped:", String(e).slice(0, 200));
    }

    // 7) Stamp a simple proof note back to milestones for quick view
    const ms = milestones;
    ms[milestoneIndex] = {
      ...(ms[milestoneIndex] || {}),
      proof: description || (files.length ? `Files:\n${files.map((f) => f.url).join("\n")}` : "") || legacyText,
    };
    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [JSON.stringify(ms), bidId]);

    // 8) Done
    return res.status(201).json(toCamel(proofRow));
  } catch (err) {
    console.error("POST /proofs error:", err);
    return res
      .status(400)
      .json({ error: "Invalid /proofs request. Check bidId, milestoneIndex, and payload format." });
  }
});

// Public: list proofs for one proposal (sanitized + geo for PublicGeoBadge)
app.get("/proofs", async (req, res) => {
  const proposalId = Number(req.query.proposalId);
  if (!Number.isFinite(proposalId)) return res.json([]); // public page expects an array

  try {
    const { rows } = await pool.query(
      `SELECT
         p.proof_id,
         p.bid_id,
         p.milestone_index,
         p.status,
         p.title,
         p.description,
         p.files,
         p.capture_time,
         p.gps_lat,
         p.gps_lon
       FROM proofs p
       JOIN bids b ON b.bid_id = p.bid_id
      WHERE b.proposal_id = $1 AND b.tenant_id = $2
      ORDER BY p.submitted_at ASC NULLS LAST, p.proof_id ASC`,
      [proposalId, req.tenantId]
    );

    const out = await Promise.all(
      rows.map(async (r) => {
        const files = Array.isArray(r.files)
          ? r.files
          : (typeof r.files === "string" ? JSON.parse(r.files || "[]") : []);
        // Safe city/state/country + rounded coords (or null if no GPS)
        const safeGeo = await buildSafeGeoForProof(r);

        return {
          proofId: r.proof_id,
          bidId: r.bid_id,
          milestoneIndex: r.milestone_index,
          status: r.status,
          title: r.title,
          publicText: r.description || null,
          files,
          takenAt: r.capture_time || null,
          location: safeGeo,            // <-- used by <PublicGeoBadge geo={p.location} ... />
        };
      })
    );

    return res.json(out);
  } catch (e) {
    console.error("GET /proofs failed:", e);
    return res.status(500).json({ error: "Failed to load proofs" });
  }
});

// Normalized proofs feed for admin UI (newest first, camelCase fields)
app.get("/proofs", adminGuard, async (req, res) => {
  try {
    let bidId = Number(req.query.bidId);
    const proposalId = Number(req.query.proposalId);

    // Fallback: resolve bidId from proposalId (so /projects/136 works even if it passes proposalId)
    if (!Number.isFinite(bidId) && Number.isFinite(proposalId)) {
      const { rows: [b] } = await pool.query(
        `SELECT bid_id FROM bids WHERE proposal_id=$1 AND tenant_id=$2 ORDER BY created_at DESC LIMIT 1`,
        [proposalId, req.tenantId]
      );
      if (b) bidId = Number(b.bid_id);
    }

    const baseSql = `
      SELECT
        proof_id,
        bid_id,
        milestone_index,
        status,
        title,
        description,
        files,
        ai_analysis,
        submitted_at,
        updated_at
      FROM proofs
    `;
    const params = [];
    const where = Number.isFinite(bidId) ? "WHERE bid_id = $1 AND tenant_id = $2" : "WHERE tenant_id = $1";
    if (Number.isFinite(bidId)) params.push(bidId);
    params.push(req.tenantId);

    const order = "ORDER BY proof_id DESC";
    const sql = [baseSql, where, order].filter(Boolean).join("\n");

    const { rows } = await pool.query(sql, params);

    const out = await Promise.all(rows.map(async (r) => ({
      proofId: Number(r.proof_id),
      bidId: Number(r.bid_id),
      milestoneIndex: Number(r.milestone_index),
      status: String(r.status || "pending"),
      title: r.title || "",
      description: r.description || "",
      files: Array.isArray(r.files) ? r.files : (r.files ? r.files : []),
      aiAnalysis: r.ai_analysis ?? null,
      submittedAt: r.submitted_at,
      updatedAt: r.updated_at,
      geoApprox: await buildSafeGeoForProof(r),
    })));

    console.log(`[GET /proofs] bidId=${Number.isInteger(bidId) ? bidId : 'ALL'} -> ${out.length}`);
    return res.json(out);
  } catch (err) {
    console.error("[GET /proofs] error:", err);
    return res.status(500).json({ error: err.message || "Internal error" });
  }
});

// Allow admin OR the bid owner (vendor) to read proofs for that bid
app.get("/proofs/:bidId", adminOrBidOwnerGuard, async (req, res) => {
  try {
    const { rows } = await pool.query(
      "SELECT * FROM proofs WHERE bid_id=$1 AND status != 'rejected' AND tenant_id=$2 ORDER BY submitted_at DESC NULLS LAST",
      [req.params.bidId, req.tenantId]
    );
    const out = await Promise.all(rows.map(async (r) => {
      const camel = toCamel(r);
      camel.geoApprox = await buildSafeGeoForProof(r); // uses gps_lat/lon if present
      return camel;
    }));
    res.json(out);
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// Approve the latest proof for a milestone (ADMIN) — robust by proof_id
app.post("/proofs/:bidId/:milestoneIndex/approve", adminGuard, async (req, res) => {
  try {
    const bidId = Number(req.params.bidId);
    const idx = Number(req.params.milestoneIndex);

    if (!Number.isInteger(bidId) || !Number.isInteger(idx)) {
      return res.status(400).json({ error: "Invalid bidId or milestoneIndex" });
    }

    // Always pick the latest by proof_id (most robust)
    const { rows: proofs } = await pool.query(
      `SELECT *
         FROM proofs
        WHERE bid_id = $1 AND milestone_index = $2 AND tenant_id = $3
        ORDER BY proof_id DESC
        LIMIT 1`,
      [bidId, idx, req.tenantId]
    );
    if (!proofs.length) {
      return res.status(404).json({ error: "No proof found for this milestone" });
    }

    const latest = proofs[0];

    // Already approved? Return as ok.
    if (String(latest.status).toLowerCase() === "approved") {
      return res.json({ ok: true, proof: toCamel(latest) });
    }

    // Mark as approved
    const { rows } = await pool.query(
      `UPDATE proofs
          SET status = 'approved', updated_at = NOW()
        WHERE proof_id = $1 AND tenant_id = $2
        RETURNING *`,
      [latest.proof_id, req.tenantId]
    );
    const updated = rows[0];
    await writeAudit(bidId, req, { proof_approved: { index: idx, proofId: updated.proof_id } });

    // Notify (admins + vendor) if enabled
    if (NOTIFY_ENABLED) {
      try {
        const { rows: [bid] } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
        if (bid) {
          const { rows: [proposal] } = await pool.query(
            "SELECT * FROM proposals WHERE proposal_id=$1",
            [bid.proposal_id]
          );
          if (proposal && typeof notifyProofApproved === "function") {
            console.log("[notify] approve about to send", { bidId, ms: idx + 1, proofId: updated.proof_id });
            await notifyProofApproved({
              proof: updated,
              bid,
              proposal,
              msIndex: idx + 1
            });
          }
        }
      } catch (e) {
        console.warn("notifyProofApproved failed (non-fatal):", String(e).slice(0, 200));
      }
    }

    return res.json({ ok: true, proof: toCamel(updated) });
  } catch (e) {
    console.error("Approve milestone proof failed:", e);
    return res.status(500).json({ error: "Internal error" });
  }
});

// Reject the latest proof for a milestone (ADMIN) — clean version
app.post("/proofs/:bidId/:milestoneIndex/reject", adminGuard, async (req, res) => {
  try {
    const bidId = Number(req.params.bidId);
    const idx = Number(req.params.milestoneIndex);
    const reason = String(req.body?.reason || req.body?.message || req.body?.note || '').trim() || null;

    if (!Number.isInteger(bidId) || !Number.isInteger(idx)) {
      return res.status(400).json({ error: "Invalid bidId or milestoneIndex" });
    }

    // Flip the LATEST proof for this (bid, milestone) to rejected
    const { rows } = await pool.query(`
      WITH latest AS (
        SELECT proof_id
          FROM proofs
         WHERE bid_id = $1 AND milestone_index = $2 AND tenant_id = $3
         ORDER BY submitted_at DESC NULLS LAST,
                  updated_at  DESC NULLS LAST,
                  proof_id    DESC
         LIMIT 1
      ), upd AS (
        UPDATE proofs p
           SET status = 'rejected',
               updated_at = NOW()
          FROM latest l
         WHERE p.proof_id = l.proof_id
         RETURNING p.*
      )
      SELECT * FROM upd;
    `, [bidId, idx, req.tenantId]);

    const updated = rows[0];
    await writeAudit(bidId, req, { proof_rejected: { index: idx, proofId: updated.proof_id, reason } });
    if (!updated) {
      return res.status(404).json({ error: "No proof found for this milestone" });
    }

    // ---- Notifications (kept INSIDE the async handler) ----
    try {
      if (process.env.NOTIFY_ENABLED === "true") {
        const { rows: bids } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
        const bid = bids[0];
        const { rows: prj } = await pool.query(
          "SELECT * FROM proposals WHERE proposal_id=$1",
          [bid.proposal_id || bid.proposalId]
        );
        const proposal = prj[0] || null;

        const subject = "❌ Proof rejected";

        const en = [
          '❌ Proof rejected',
          `Project: ${proposal?.title || proposal?.name || proposal?.proposal_id}`,
          `Bid: ${bidId} • Milestone: ${idx}`,
          reason ? `Reason: ${reason}` : ''
        ].filter(Boolean).join('\n');

        const es = [
          '❌ Prueba rechazada',
          `Proyecto: ${proposal?.title || proposal?.name || proposal?.proposal_id}`,
          `Oferta: ${bidId} • Hito: ${idx}`,
          reason ? `Motivo: ${reason}` : ''
        ].filter(Boolean).join('\n');

        const { text: msg, html } = bi(en, es);

        const { rows: vprows } = await pool.query(
          `SELECT email, phone, telegram_chat_id
             FROM vendor_profiles
            WHERE lower(wallet_address)=lower($1)
            LIMIT 1`,
          [(bid.wallet_address || "").toLowerCase()]
        );
        const vp = vprows[0] || {};
        const vendorEmail = (vp.email || "").trim();
        const vendorPhone = (vp.phone || "").trim();
        const vendorTg = (vp.telegram_chat_id || "").trim();

        const waVars = {
          "1": `${proposal?.title || "(untitled)"} — ${proposal?.org_name || ""}`,
          "2": `${bid.vendor_name || ""} (${bid.wallet_address || ""})`,
          "3": `#${idx}`,
          "4": reason ? reason : "No reason provided"
        };

        await Promise.all(
          [
            TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, msg) : null,
            ...(TWILIO_WA_CONTENT_SID
              ? (ADMIN_WHATSAPP || []).map(n => sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, waVars))
              : (ADMIN_WHATSAPP || []).map(n => sendWhatsApp(n, msg))),
            MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,

            // Vendor
            vendorTg ? sendTelegram([vendorTg], msg) : null,
            vendorEmail ? sendEmail([vendorEmail], subject, html) : null,
            vendorPhone
              ? (TWILIO_WA_CONTENT_SID
                ? sendWhatsAppTemplate(vendorPhone, TWILIO_WA_CONTENT_SID, waVars)
                : sendWhatsApp(vendorPhone, msg))
              : null,
          ].filter(Boolean)
        );
      }
    } catch (e) {
      console.warn("notify-on-reject (proofs route) failed:", String(e).slice(0, 200));
    }
    // -------------------------------------------------------

    return res.json({ ok: true, proof: toCamel(updated) });
  } catch (e) {
    console.error("Reject milestone proof failed (proofs route):", e);
    return res.status(500).json({ error: "Internal error" });
  }
});

// --- EXIF date normalization + extraction (robust) ---
function normExifDate(raw) {
  if (!raw) return null;
  const s = String(raw).trim();

  // EXIF style: 2024:09:30 14:22:11(.sss optional)
  let m = s.match(/^(\d{4}):(\d{2}):(\d{2})[ T](\d{2}):(\d{2}):(\d{2})(?:\.\d+)?$/);
  if (m) {
    const iso = `${m[1]}-${m[2]}-${m[3]}T${m[4]}:${m[5]}:${m[6]}Z`;
    const d = new Date(iso);
    return Number.isNaN(d.getTime()) ? null : d.toISOString();
  }

  // ISO-ish already?
  const d2 = new Date(s);
  if (!Number.isNaN(d2.getTime())) return d2.toISOString();

  return null;
}
function pick(obj, ...keys) {
  for (const k of keys) {
    if (obj && obj[k] != null && obj[k] !== '') return obj[k];
  }
  return null;
}
function extractAnyDateFromExif(exif) {
  if (!exif || typeof exif !== 'object') return null;

  // Common fields (both cases)
  const direct =
    pick(exif,
      'createDate', 'CreateDate',
      'dateTimeOriginal', 'DateTimeOriginal',
      'modifyDate', 'ModifyDate',
      'dateTime', 'DateTime'
    ) ||
    // sometimes nested
    pick(exif?.Photo || {}, 'DateTimeOriginal') ||
    pick(exif?.ExifIFD || {}, 'DateTimeOriginal') ||
    pick(exif?.QuickTime || {}, 'CreateDate');

  let iso = normExifDate(direct);
  if (iso) return iso;

  // GPS date+time pair
  if (exif.GPSDateStamp && exif.GPSTimeStamp) {
    iso = normExifDate(`${exif.GPSDateStamp} ${exif.GPSTimeStamp}`);
    if (iso) return iso;
  }

  // Fallback: scan all string values that look like dates
  const stack = [exif];
  const seen = new Set();
  while (stack.length) {
    const cur = stack.pop();
    if (!cur || typeof cur !== 'object' || seen.has(cur)) continue;
    seen.add(cur);
    for (const v of Object.values(cur)) {
      if (typeof v === 'string') {
        const tryIso = normExifDate(v);
        if (tryIso) return tryIso;
      } else if (v && typeof v === 'object') {
        stack.push(v);
      }
    }
  }
  return null;
}
function deriveCaptureFromMeta(fileMeta) {
  const arr = Array.isArray(fileMeta) ? fileMeta : [];
  for (const m of arr) {
    const iso = extractAnyDateFromExif(m?.exif || {});
    if (iso) return iso;
  }
  return null;
}
function asArrayJson(v) {
  if (Array.isArray(v)) return v;
  if (typeof v === 'string') {
    try { const j = JSON.parse(v); return Array.isArray(j) ? j : []; } catch { return []; }
  }
  return [];
}

// ==============================
// Public — Geo feed (no auth)
// ==============================
app.get("/public/geo/:bidId", async (req, res) => {
  try {
    const bidId = Number(req.params.bidId);
    if (!Number.isInteger(bidId)) {
      return res.status(400).json({ error: "Invalid bidId" });
    }

    // NOTE: must select file_meta + capture_time for the takenAt value
    const { rows } = await pool.query(
      `SELECT
         proof_id, bid_id, milestone_index, status, title,
         submitted_at, updated_at,
         file_meta, capture_time,
         gps_lat, gps_lon, gps_alt
       FROM proofs
       WHERE bid_id = $1 AND status != 'rejected'
       ORDER BY proof_id DESC`,
      [bidId]
    );

    const out = await Promise.all(rows.map(async (r) => {
      // derive from EXIF if capture_time is missing
      let meta = [];
      if (Array.isArray(r.file_meta)) meta = r.file_meta;
      else if (typeof r.file_meta === "string") {
        try { meta = JSON.parse(r.file_meta) || []; } catch { meta = []; }
      }
      const derived = deriveCaptureFromMeta(meta);  // <-- requires helpers below
      const captureTime = r.capture_time || derived || null;

      return {
        proofId: Number(r.proof_id),
        bidId: Number(r.bid_id),
        milestoneIndex: Number(r.milestone_index),
        status: String(r.status || "pending"),
        title: r.title || "",
        submittedAt: r.submitted_at,
        updatedAt: r.updated_at,
        geoApprox: await buildSafeGeoForProof(r),
        captureTime, // <-- frontend reads this as takenAt
      };
    }));

    res.json(out);
  } catch (e) {
    console.error("[GET /public/geo/:bidId] error:", e);
    res.status(500).json({ error: "Internal error" });
  }
});

app.get("/public/geo/proof/:proofId", async (req, res) => {
  try {
    const proofId = Number(req.params.proofId);
    if (!Number.isFinite(proofId)) return res.status(400).json({ error: "Invalid proofId" });

    const { rows } = await pool.query(
      `SELECT proof_id, bid_id, milestone_index, status, title, submitted_at, updated_at,
              gps_lat, gps_lon, gps_alt
         FROM proofs
        WHERE proof_id = $1
        LIMIT 1`,
      [proofId]
    );
    if (!rows[0]) return res.status(404).json({ error: "Proof not found" });

    const r = rows[0];
    res.json({
      proofId: Number(r.proof_id),
      bidId: Number(r.bid_id),
      milestoneIndex: Number(r.milestone_index),
      status: String(r.status || "pending"),
      title: r.title || "",
      submittedAt: r.submitted_at,
      updatedAt: r.updated_at,
      geoApprox: await buildSafeGeoForProof(r),
    });
  } catch (e) {
    console.error("[GET /public/geo/proof/:proofId] error:", e);
    res.status(500).json({ error: "Internal error" });
  }
});

// --- Latest proof status per milestone for a bid --------------------------------
app.get('/bids/:bidId/proofs/latest-status', adminGuard, async (req, res) => {
  try {
    const bidId = Number(req.params.bidId);
    if (!Number.isFinite(bidId)) return res.status(400).json({ error: 'Invalid bid id' });

    // Debug log so you can confirm it's hit from the admin page
    console.log('[latest-status] GET', { bidId, user: req.user?.sub, role: req.user?.role });

    // Pick the most recent proof per milestone (submitted_at, then updated_at, then id)
    const { rows } = await pool.query(`
      WITH ranked AS (
        SELECT
          milestone_index,
          status,
          ROW_NUMBER() OVER (
            PARTITION BY milestone_index
            ORDER BY submitted_at DESC NULLS LAST,
                     updated_at  DESC NULLS LAST,
                     proof_id    DESC
          ) AS rn
        FROM proofs
        WHERE bid_id = $1 AND tenant_id = $2
      )
      SELECT milestone_index, status
      FROM ranked
      WHERE rn = 1
    `, [bidId, req.tenantId]);

    const byIndex = {};
    for (const r of rows) {
      byIndex[Number(r.milestone_index)] = String(r.status || 'pending');
    }

    res.set('Cache-Control', 'no-store');
    return res.json({ byIndex });
  } catch (e) {
    console.error('[latest-status] error', e);
    return res.status(500).json({ error: 'Internal error' });
  }
});

// Re-run Agent2 on a single proof (admin only)
app.all('/proofs/:id/analyze', (req, res, next) => {
  if (req.method === 'POST') return next();
  if (req.method === 'OPTIONS') {
    res.set('Allow', 'POST, OPTIONS');
    return res.sendStatus(204);
  }
  res.set('Allow', 'POST, OPTIONS');
  return res.status(405).json({ error: 'Method Not Allowed. Use POST /proofs/:id/analyze.' });
});

app.post('/proofs/:id/analyze', adminGuard, async (req, res) => {
  const proofId = Number(req.params.id);
  if (!Number.isFinite(proofId)) return res.status(400).json({ error: 'Invalid proof id' });

  try {
    // 1) Load proof
    const { rows: pr } = await pool.query('SELECT * FROM proofs WHERE proof_id=$1 AND tenant_id=$2', [proofId, req.tenantId]);
    const proof = pr[0];
    if (!proof) return res.status(404).json({ error: 'Proof not found' });
    const proofDesc = String(proof.description || '').trim();

    // 2) Load bid + proposal for context
    const { rows: br } = await pool.query('SELECT * FROM bids WHERE bid_id=$1', [proof.bid_id]);
    const bid = br[0];
    if (!bid) return res.status(404).json({ error: 'Bid not found for proof' });

    const { rows: por } = await pool.query('SELECT * FROM proposals WHERE proposal_id=$1', [bid.proposal_id]);
    const proposal = por[0] || null;

    // 3) Build prompt inputs
    const vendorPrompt = typeof req.body?.prompt === 'string' ? req.body.prompt.trim() : '';
    const files = Array.isArray(proof.files)
      ? proof.files
      : (typeof proof.files === 'string' ? JSON.parse(proof.files || '[]') : []);
    const description = String(proof.description || '').slice(0, 2000);

    // --- EXIF/GPS prep from the saved proof row ---
    const meta = Array.isArray(proof.file_meta)
      ? proof.file_meta
      : (typeof proof.file_meta === "string" ? JSON.parse(proof.file_meta || "[]") : []);

    const gpsItems = meta.filter(m =>
      Number.isFinite(m?.exif?.gpsLatitude) && Number.isFinite(m?.exif?.gpsLongitude)
    );
    const gpsCount = gpsItems.length;
    const firstGps = gpsItems[0]
      ? {
        lat: Number(gpsItems[0].exif.gpsLatitude),
        lon: Number(gpsItems[0].exif.gpsLongitude),
        alt: Number.isFinite(Number(gpsItems[0].exif?.gpsAltitude))
          ? Number(gpsItems[0].exif.gpsAltitude)
          : null,
      }
      : { lat: null, lon: null, alt: null };

    const captureIso = proof.capture_time || null; // we saved this on submit
    const lat = Number.isFinite(firstGps?.lat) ? firstGps.lat : (Number.isFinite(proof.gps_lat) ? Number(proof.gps_lat) : null);
    const lon = Number.isFinite(firstGps?.lon) ? firstGps.lon : (Number.isFinite(proof.gps_lon) ? Number(proof.gps_lon) : null);

    let rgeo = null;
    if (Number.isFinite(lat) && Number.isFinite(lon)) {
      try { rgeo = await reverseGeocode(lat, lon); } catch { }
    }
    const metaBlock = summarizeMeta(meta);
    const capNote = captureIso
      ? `First capture time (EXIF, ISO8601): ${captureIso}`
      : 'No capture time in EXIF.';
    const gpsNote = gpsCount
      ? `GPS present in ${gpsCount} file(s). First fix: ${firstGps.lat}, ${firstGps.lon}${firstGps.alt != null ? ` • alt ${firstGps.alt}m` : ''}`
      : 'No GPS in submitted media.';

    // Milestone info for this proof
    const msArr = Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || "[]");
    const ms = msArr[proof.milestone_index] || {};

    // 4) Base prompt (now includes EXIF/GPS + capture time block)
    const basePrompt = `
You are Agent2. Evaluate a vendor's submitted proof for a specific milestone.

Return strict JSON:
{
  "summary": string,
  "evidence": string[],
  "gaps": string[],
  "fit": "low" | "medium" | "high",
  "confidence": number,
  "geo": {
    "gpsCount": number,
    "firstFix": { "lat": number|null, "lon": number|null, "alt": number|null },
    "captureTime": string|null
  }
}

Context:
- Proposal: ${proposal?.title || "(unknown)"} (${proposal?.org_name || "(unknown)"})
- Milestone: ${ms?.name || "(unknown)"} — $${ms?.amount ?? "?"}
- Vendor: ${bid.vendor_name || "(unknown)"}

Proof title: ${proof.title || "(untitled)"}
Proof description (truncated):
"""${description}"""

Files:
${files.map((f) => `- ${f.name || "file"}: ${f.url}`).join("\n") || "(none)"}

MEDIA METADATA (EXIF/GPS summary):
${metaBlock}

Hints:
- ${gpsNote}
- ${capNote}
`.trim();

    const fullPrompt = vendorPrompt ? `${vendorPrompt}\n\n---\n${basePrompt}` : basePrompt;

    // 5) Run OpenAI (or fallback)
    let analysis;
    if (!openai) {
      analysis = {
        summary: "OpenAI not configured; no automatic proof analysis.",
        evidence: [],
        gaps: [],
        fit: "low",
        confidence: 0,
        geo: { gpsCount, firstFix: firstGps, captureTime: captureIso || null },
      };
    } else {
      const resp = await openai.chat.completions.create({
        model: "gpt-4o-mini",
        temperature: 0.2,
        messages: [{ role: "user", content: fullPrompt }],
        response_format: { type: "json_object" },
      });

      try {
        const raw = resp.choices?.[0]?.message?.content || "{}";
        analysis = JSON.parse(raw);
      } catch {
        analysis = { summary: "Agent2 returned non-JSON.", evidence: [], gaps: [], fit: "low", confidence: 0 };
      }
    } // ← end else

    // ↓↓↓ THIS BLOCK GOES OUTSIDE the else, before the DB UPDATE ↓↓↓

    // Ensure geo always present
    if (!analysis.geo) {
      analysis.geo = { gpsCount, firstFix: firstGps, captureTime: captureIso || null };
    }

    // Attach GPS + human-readable location (uses the `lat`/`lon` you computed above)
    analysis.geo.lat = Number.isFinite(lat) ? lat : (analysis.geo.lat ?? null);
    analysis.geo.lon = Number.isFinite(lon) ? lon : (analysis.geo.lon ?? null);
    if (captureIso && !analysis.geo.captureTime) analysis.geo.captureTime = captureIso;

    if (rgeo) {
      Object.assign(analysis.geo, {
        // handle either new {provider,label} or older {source,displayName}
        provider: rgeo.provider || rgeo.source || null,
        address: rgeo.label || rgeo.displayName || null,
        country: rgeo.country ?? null,
        state: rgeo.state || rgeo.region || null,
        county: rgeo.county || rgeo.province || null,
        city: rgeo.city || rgeo.municipality || null,
        suburb: rgeo.suburb ?? null,
        postcode: rgeo.postcode ?? null,
      });
    }

    // (optional) add a readable line to the summary
    const locBits = [analysis.geo.city, analysis.geo.state, analysis.geo.country].filter(Boolean);
    if (locBits.length) {
      const locLine = `Location: ${locBits.join(", ")} (${analysis.geo.lat?.toFixed?.(6)}, ${analysis.geo.lon?.toFixed?.(6)})`;
      if (!String(analysis.summary || "").includes(locLine)) {
        analysis.summary = `${analysis.summary ? analysis.summary.trim() + "\n\n" : ""}${locLine}`;
      }
    }

    // 6) Save & return
    const { rows: upd } = await pool.query(
      'UPDATE proofs SET ai_analysis=$1, updated_at=NOW() WHERE proof_id=$2 RETURNING *',
      [JSON.stringify(analysis), proofId]
    );
    return res.json(toCamel(upd[0]));
  } catch (e) {
    console.error('proof analyze error:', e);
    return res.status(500).json({ error: 'Failed to analyze proof' });
  }
});

// Reject the latest proof for a milestone (ADMIN)
// URL: POST /bids/:bidId/milestones/:idx/reject
app.post("/bids/:bidId/milestones/:idx/reject", adminGuard, async (req, res) => {
  try {
    const bidId = Number(req.params.bidId);
    const idx = Number(req.params.idx);
    const reason = (req.body && req.body.reason) ? String(req.body.reason).slice(0, 500) : null;

    if (!Number.isInteger(bidId) || !Number.isInteger(idx)) {
      return res.status(400).json({ error: "bad bidId or milestone index" });
    }

    // Find the most recent proof for this milestone
    const { rows: proofs } = await pool.query(
      `SELECT proof_id FROM proofs
         WHERE bid_id = $1 AND milestone_index = $2 AND tenant_id = $3
         ORDER BY submitted_at DESC NULLS LAST, updated_at DESC NULLS LAST
         LIMIT 1`,
      [bidId, idx, req.tenantId]
    );
    if (!proofs.length) return res.status(404).json({ error: "No proof found for this milestone" });

    const proofId = proofs[0].proof_id;

    // Mark as rejected
    const { rows } = await pool.query(
      `UPDATE proofs
         SET status = 'rejected', updated_at = NOW()
       WHERE proof_id = $1 AND tenant_id = $2
       RETURNING proof_id, bid_id, milestone_index, status, updated_at`,
      [proofId, req.tenantId]
    );

    // Notify
    try {
      if (process.env.NOTIFY_ENABLED === "true") {
        const { rows: pr } = await pool.query("SELECT * FROM proofs WHERE proof_id=$1", [proofId]);
        const proof = pr[0];
        const { rows: bids } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
        const bid = bids[0];
        const { rows: prj } = await pool.query(
          "SELECT * FROM proposals WHERE proposal_id=$1",
          [bid.proposal_id || bid.proposalId]
        );
        const proposal = prj[0] || null;

        const subject = "❌ Proof rejected";
        const msg = [
          "❌ Proof rejected",
          `Project: ${proposal?.title || proposal?.name || proposal?.proposal_id}`,
          `Bid: ${bidId} • Milestone: ${idx}`,
          reason ? `Reason: ${reason}` : ""
        ].filter(Boolean).join("\n");
        const html = msg.replace(/\n/g, "<br>");

        // Load vendor contacts (email/phone/telegram) from vendor_profiles
        const { rows: vprows } = await pool.query(
          `SELECT email, phone, telegram_chat_id
         FROM vendor_profiles
        WHERE lower(wallet_address)=lower($1)
        LIMIT 1`,
          [(bid.wallet_address || "").toLowerCase()]
        );
        const vp = vprows[0] || {};
        const vendorEmail = (vp.email || "").trim();
        const vendorPhone = (vp.phone || "").trim();
        const vendorTg = (vp.telegram_chat_id || "").trim();

        // WhatsApp template variables (if TWILIO_WA_CONTENT_SID is set)
        const waVars = {
          "1": `${proposal?.title || "(untitled)"} — ${proposal?.org_name || ""}`,
          "2": `${bid.vendor_name || ""} (${bid.wallet_address || ""})`,
          "3": `#${idx}`,
          "4": reason ? reason : "No reason provided"
        };

        await Promise.all(
          [
            // Admins
            TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, msg) : null,
            ...(TWILIO_WA_CONTENT_SID
              ? (ADMIN_WHATSAPP || []).map(n => sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, waVars))
              : (ADMIN_WHATSAPP || []).map(n => sendWhatsApp(n, msg))),
            MAIL_ADMIN_TO?.length ? sendEmail(MAIL_ADMIN_TO, subject, html) : null,

            // Vendor (email + optional TG/WA)
            vendorTg ? sendTelegram([vendorTg], msg) : null,
            vendorEmail ? sendEmail([vendorEmail], subject, html) : null,
            vendorPhone
              ? (TWILIO_WA_CONTENT_SID
                ? sendWhatsAppTemplate(vendorPhone, TWILIO_WA_CONTENT_SID, waVars)
                : sendWhatsApp(vendorPhone, msg))
              : null,
          ].filter(Boolean)
        );
      }
    } catch (e) {
      console.warn("notify-on-reject failed (non-fatal):", String(e).slice(0, 200));
    }

    return res.json({ ok: true, proof: rows[0] });
  } catch (e) {
    console.error("Reject milestone proof failed:", e);
    return res.status(500).json({ error: "Internal error" });
  }
});

// --- Vendor-safe: Archive a proof -------------------------------------------
// POST /proofs/:id/archive
// Auth: admin OR vendor who owns the bid (wallet matches)
app.post('/proofs/:id/archive', authRequired, async (req, res) => {
  const proofId = Number(req.params.id);
  if (!Number.isFinite(proofId)) {
    return res.status(400).json({ error: 'Invalid proof id' });
  }

  try {
    // Load proof + owning bid (to verify ownership)
    const { rows } = await pool.query(
      `SELECT p.proof_id, p.bid_id, p.milestone_index, p.status,
              b.wallet_address AS bid_wallet
         FROM proofs p
         JOIN bids b ON b.bid_id = p.bid_id
        WHERE p.proof_id = $1 AND p.tenant_id = $2`,
      [proofId, req.tenantId]
    );
    const pr = rows[0];
    if (!pr) return res.status(404).json({ error: 'Proof not found' });

    const caller = String(req.user?.sub || '').toLowerCase();
    const isAdmin = String(req.user?.role || '').toLowerCase() === 'admin';
    const owner = String(pr.bid_wallet || '').toLowerCase();

    if (!isAdmin && !caller) return res.status(401).json({ error: 'Unauthorized' });
    if (!isAdmin && caller !== owner) return res.status(403).json({ error: 'Forbidden' });

    if (String(pr.status || '').toLowerCase() === 'archived') {
      return res.json({ ok: true, proof: toCamel(pr) });
    }

    const { rows: upd } = await pool.query(
      `UPDATE proofs
          SET status = 'archived', updated_at = NOW()
        WHERE proof_id = $1 AND tenant_id = $2
        RETURNING *`,
      [proofId, req.tenantId]
    );

    return res.json({ ok: true, proof: toCamel(upd[0]) });
  } catch (err) {
    console.error('archive proof error:', err);
    return res.status(500).json({ error: 'Internal error archiving proof' });
  }
});

// --- Agent2 Chat about a SPECIFIC PROOF (SSE) -------------------------------
app.all('/proofs/:id/chat', (req, res, next) => {
  if (req.method === 'POST') return next();
  if (req.method === 'OPTIONS') {
    res.set('Allow', 'POST, OPTIONS');
    return res.sendStatus(204);
  }
  res.set('Allow', 'POST, OPTIONS');
  return res.status(405).json({ error: 'Method Not Allowed. Use POST /proofs/:id/chat.' });
});

// NOTE: keep adminGuard, or relax to adminOrBidOwnerGuard if vendors should access their own proofs.
app.post('/proofs/:id/chat', adminGuard, async (req, res) => {
  if (!openai) return res.status(503).json({ error: 'OpenAI not configured' });

  const proofId = Number(req.params.id);
  if (!Number.isFinite(proofId)) return res.status(400).json({ error: 'Invalid proof id' });

  // SSE headers
  res.set({
    'Content-Type': 'text/event-stream; charset=utf-8',
    'Cache-Control': 'no-cache, no-transform',
    'Connection': 'keep-alive',
  });
  if (typeof res.flushHeaders === 'function') res.flushHeaders();

  try {
    // 1) Load proof
    const { rows: pr } = await pool.query('SELECT * FROM proofs WHERE proof_id=$1 AND tenant_id=$2', [proofId, req.tenantId]);
    const proof = pr[0];
    if (!proof) {
      res.write(`data: ERROR Proof not found\n\n`);
      res.write(`data: [DONE]\n\n`);
      return res.end();
    }

    // 2) Load bid + proposal
    const { rows: br } = await pool.query('SELECT * FROM bids WHERE bid_id=$1', [proof.bid_id]);
    const bid = br[0];
    if (!bid) {
      res.write(`data: ERROR Bid not found for proof\n\n`);
      res.write(`data: [DONE]\n\n`);
      return res.end();
    }

    const { rows: por } = await pool.query('SELECT * FROM proposals WHERE proposal_id=$1', [bid.proposal_id]);
    const proposal = por[0] || null;

    // 3) Normalize proof payload (single source of truth)
    const files = Array.isArray(proof?.files)
      ? proof.files
      : (typeof proof?.files === 'string' ? JSON.parse(proof.files || '[]') : []);

    const meta = Array.isArray(proof?.file_meta)
      ? proof.file_meta
      : (typeof proof?.file_meta === 'string' ? JSON.parse(proof.file_meta || '[]') : []);

    const metaBlock = summarizeMeta(meta);

    // === A) Proof description string ===
    const proofDesc = String(proof?.description || '').trim();

    // === B) Extract PDF text from any proof files ===
    const pinataJwt = await tenantService.getTenantConfig(req.tenantId, 'pinata_jwt');
    let pdfText = '';
    for (const f of files) {
      if (!f?.url) continue;
      const info = await waitForPdfInfoFromDoc({ url: f.url, name: f.name || '' }, {}, pinataJwt);
      if (info.used && info.text) {
        pdfText += `\n\n[${f.name || 'file'}]\n${info.text}`;
      }
    }
    pdfText = pdfText.trim();

    // === C) Build location block from AI geo or GPS (+ reverse geocode) ===
    let aiGeo = null;
    try { aiGeo = JSON.parse(proof?.ai_analysis || '{}')?.geo || null; } catch { }

    const lat = Number.isFinite(aiGeo?.lat) ? Number(aiGeo.lat)
      : (Number.isFinite(proof?.gps_lat) ? Number(proof.gps_lat) : null);
    const lon = Number.isFinite(aiGeo?.lon) ? Number(aiGeo.lon)
      : (Number.isFinite(proof?.gps_lon) ? Number(proof.gps_lon) : null);

    let rgeo = null;
    if (Number.isFinite(lat) && Number.isFinite(lon)) {
      try { rgeo = await reverseGeocode(lat, lon); } catch { }
    }

    const loc = {
      lat, lon,
      country: aiGeo?.country ?? rgeo?.country ?? null,
      state: aiGeo?.state ?? rgeo?.state ?? null,
      county: aiGeo?.county ?? rgeo?.county ?? null,
      city: aiGeo?.city ?? rgeo?.city ?? null,
      suburb: aiGeo?.suburb ?? rgeo?.suburb ?? null,
      postcode: aiGeo?.postcode ?? rgeo?.postcode ?? null,
      address: aiGeo?.address ?? rgeo?.displayName ?? rgeo?.label ?? null,
      provider: aiGeo?.provider ?? rgeo?.provider ?? rgeo?.source ?? null,
    };

    const locationBlock = loc ? [
      'Known location:',
      (Number.isFinite(loc.lat) && Number.isFinite(loc.lon))
        ? `- Coords: ${loc.lat.toFixed(6)}, ${loc.lon.toFixed(6)}`
        : '- Coords: n/a',
      loc.address ? `- Address: ${loc.address}` : '',
      loc.city ? `- City: ${loc.city}` : '',
      loc.state ? `- State/Region: ${loc.state}` : '',
      loc.country ? `- Country: ${loc.country}` : '',
      loc.provider ? `- Source: ${loc.provider}` : '',
    ].filter(Boolean).join('\n') : 'Known location: (none)';

    const userText = String(req.body?.message || 'Analyze this proof for completeness and risks.').slice(0, 2000);

    // Gather any images from proof; also BEFORE images from proposal docs (if present)
    const proposalImages = collectProposalImages(proposal);
    const proofImages = files.filter(isImageFile);
    const hasAnyImages = proposalImages.length > 0 || proofImages.length > 0;

    // 4) Create context block
    const context = [
      'You are Agent 2 for LithiumX.',
      'Answer ONLY using the provided bid/proposal fields and the submitted proof (description + extracted PDF text).',
      'If something is not present in that material, say it is not stated in the submitted proof.',
      '',
      '--- PROPOSAL ---',
      JSON.stringify({
        org: proposal?.org_name || '',
        title: proposal?.title || '',
        summary: proposal?.summary || '',
        budgetUSD: proposal?.amount_usd ?? 0,
      }, null, 2),
      '',
      '--- BID ---',
      JSON.stringify({
        vendor: bid.vendor_name || '',
        priceUSD: bid.price_usd ?? 0,
        days: bid.days ?? 0,
        notes: bid.notes || '',
        milestones: (Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || '[]')),
      }, null, 2),
      '',
      '--- PROOF ---',
      JSON.stringify({
        title: proof?.title || '',
        description: proofDesc.slice(0, 4000),
        files: files.map(f => ({ name: f.name, url: f.url })),
      }, null, 2),
      '',
      '--- IMAGE/VIDEO METADATA ---',
      metaBlock,
      '',

      // >>> INSERTED LINES <<<
      '--- KNOWN LOCATION ---',
      locationBlock,
      '',
      // <<< END INSERTION <<<

      pdfText
        ? `--- PROOF PDF TEXT (truncated) ---\n${pdfText.slice(0, 15000)}`
        : `--- NO PDF TEXT AVAILABLE ---`,
    ].join('\n');

    // ——— FIX: Base64 Proxy for Proof Chat (Prevents Timeouts) ———
    const urlToContent = async (f) => {
      const name = (f.name || f.url || "").toLowerCase();
      const mime = (f.mimetype || "").toLowerCase();
      if (!mime.startsWith("image/") && !/\.(jpe?g|png|webp|gif)$/.test(name)) return null;

      try {
        // Clean URL & Force Cloudflare (Fastest Download)
        let url = (f.url || "").trim().replace(/[.,;]+$/, "");
        url = url.replace("gateway.pinata.cloud", "cf-ipfs.com");

        // Download buffer using your robust fetcher
        const buf = await fetchAsBuffer(url);
        const b64 = buf.toString('base64');
        let finalMime = mime.startsWith("image/") ? mime : "image/jpeg";

        return { type: 'image_url', image_url: { url: `data:${finalMime};base64,${b64}` } };
      } catch (e) {
        console.warn(`[ProofChat] Skipped image ${f.url}:`, e.message);
        return null;
      }
    };

    // 5) Choose vision vs text model
    let stream;
    if (hasAnyImages) {
      const systemMsg = `
You are Agent2 for LithiumX.
You CAN analyze the attached images.
Task: Compare "BEFORE" (proposal) vs "AFTER" (proof) images to assess progress.

CRITICAL INSTRUCTION:
- You MUST cross-reference the "IMAGE/VIDEO METADATA" and "KNOWN LOCATION" sections provided in the Context below.
- If GPS coordinates or dates are present in the metadata, mention them in your evidence.

ALWAYS provide:
1) 1–2 sentence conclusion.
2) Bullets with:
   • Evidence (Visual cues, materials, etc.)
   • Location Verification (Does the GPS/Metadata match the project?)
   • Differences/Progress
   • Inconsistencies
   • Confidence [0–1]
`.trim();

      const userContent = [
        { type: 'text', text: `User request: ${userText}\n\nCompare BEFORE (proposal docs) vs AFTER (proof) images.` },
      ];

      // Process BEFORE Images (Proposal) - Limit 3
      const beforeImgs = proposalImages.slice(0, 3);
      const beforeProcessed = await Promise.all(beforeImgs.map(urlToContent));
      const validBefore = beforeProcessed.filter(Boolean);

      if (validBefore.length > 0) {
        userContent.push({ type: 'text', text: 'BEFORE (from proposal):' });
        userContent.push(...validBefore);
      } else {
        userContent.push({ type: 'text', text: 'BEFORE: (none available)' });
      }

      // Process AFTER Images (Proof) - Limit 3
      const afterImgs = proofImages.slice(0, 3);
      const afterProcessed = await Promise.all(afterImgs.map(urlToContent));
      const validAfter = afterProcessed.filter(Boolean);

      if (validAfter.length > 0) {
        userContent.push({ type: 'text', text: 'AFTER (from proof):' });
        userContent.push(...validAfter);
      } else {
        userContent.push({ type: 'text', text: 'AFTER: (none available)' });
      }

      userContent.push({ type: 'text', text: `\n\n--- CONTEXT ---\n${context}` });

      console.log(`[ProofChat] Sending Vision request: ${validBefore.length} before + ${validAfter.length} after.`);

      stream = await openai.chat.completions.create({
        model: 'gpt-4o-mini',
        temperature: 0.2,
        stream: true,
        messages: [
          { role: 'system', content: systemMsg },
          { role: 'user', content: userContent },
        ],
      });

    } else {
      // Text-only fallback (unchanged)
      stream = await openai.chat.completions.create({
        model: 'gpt-4o-mini',
        temperature: 0.2,
        stream: true,
        messages: [
          { role: 'system', content: 'Be concise. Cite specific items from the provided proof context.' },
          { role: 'user', content: `${userText}\n\n--- CONTEXT ---\n${context}` },
        ],
      });
    }

    // 6) Stream tokens
    let full = '';
    for await (const part of stream) {
      const token = part?.choices?.[0]?.delta?.content || '';
      if (token) {
        full += token;
        res.write(`data: ${token}\n\n`);
      }
    }

    // 7) Footer: low-confidence hint + next checks
    const conf = extractConfidenceFromText(full);
    const nextChecks = buildNextChecks({
      hasAnyPdfText: false,
      imageCount: proofImages.length,
      ocrSeen: /[A-Za-z0-9]{3,}/.test(full || '')
    });

    if (conf !== null && conf < 0.35) {
      res.write(`data: \n\n`);
      res.write(`data: 🔎 Needs human review (low confidence: ${conf.toFixed(2)})\n\n`);
    }
    if (nextChecks.length) {
      res.write(`data: \n\n`);
      res.write(`data: Next checks:\n\n`);
      for (const item of nextChecks) res.write(`data: • ${item}\n\n`);
    }

    res.write(`data: [DONE]\n\n`);
    res.end();
  } catch (err) {
    console.error('/proofs/:id/chat SSE error:', err);
    try {
      res.write(`data: ERROR ${String(err).slice(0, 200)}\n\n`);
      res.write(`data: [DONE]\n\n`);
      res.end();
    } catch { }
  }
});

// ==============================
// Routes — Vendor profile (fill once, used in Admin Vendors)
// ==============================
const profileSchema = Joi.object({
  vendorName: Joi.string().min(2).max(140).required(),
  email: Joi.string().email().allow(''),
  phone: Joi.string().allow(''),
  address: Joi.alternatives().try(
    Joi.string().allow(''),
    Joi.object({
      line1: Joi.string().allow(''),
      city: Joi.string().allow(''),
      country: Joi.string().allow(''),
      postalCode: Joi.string().allow(''),
    })
  ).default(''),
  website: Joi.string().allow(''),
});

// helpers (add once near your other helpers if missing)
function normWebsite(s) {
  if (!s) return null;
  s = String(s).trim();
  if (!s) return null;
  return /^https?:\/\//i.test(s) ? s : `https://${s}`;
}
function _addrText(a, city, country) {
  if (!a) return null;
  if (typeof a === 'string') {
    const line = a.trim();
    return [line, city || '', country || ''].filter(Boolean).join(', ') || line || null;
  }
  if (typeof a === 'object') {
    const line = a.line1 || a.address1 || '';
    const cty = a.city || city || '';
    const ctry = a.country || country || '';
    return [line, cty, ctry].filter(Boolean).join(', ') || null;
  }
  return null;
}

// ---- Save generic profile (NO vendor insert here) ----
app.post("/profile", authRequired, async (req, res) => {
  try {
    const wallet = String(req.user?.sub || "").toLowerCase();
    if (!wallet) return res.status(401).json({ error: "unauthorized" });

    const b = req.body || {};
    const displayName =
      (b.vendorName ?? b.orgName ?? b.displayName ?? b.display_name ?? "").trim();

    const addrText = _addrText(b.address, b.city, b.country);

    await pool.query(
      `
      INSERT INTO user_profiles
        (wallet_address, display_name, email, phone, website, address, city, country, telegram_chat_id, whatsapp, updated_at)
      VALUES
        ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,NOW())
      ON CONFLICT (wallet_address) DO UPDATE SET
        display_name      = COALESCE(NULLIF(EXCLUDED.display_name,''), user_profiles.display_name),
        email             = EXCLUDED.email,
        phone             = EXCLUDED.phone,
        website           = EXCLUDED.website,
        address           = EXCLUDED.address,
        city              = EXCLUDED.city,
        country           = EXCLUDED.country,
        telegram_chat_id  = EXCLUDED.telegram_chat_id,
        whatsapp          = EXCLUDED.whatsapp,
        updated_at        = NOW()
      `,
      [
        wallet,
        displayName || null,
        b.email ?? null,
        b.phone ?? null,
        normWebsite(b.website) ?? null,
        addrText,
        b.address?.city ?? b.city ?? null,
        b.address?.country ?? b.country ?? null,
        b.telegramChatId ?? b.telegram_chat_id ?? null,
        b.whatsapp ?? null,
      ]
    );

    return res.json({ ok: true });
  } catch (e) {
    console.error("POST /profile error", e);
    return res.status(500).json({ error: "profile_save_failed" });
  }
});

// ---------- address helper (place this ABOVE the /vendor/profile route) ----------
function _addrObj(addr, city = null, country = null) {
  let o;
  if (addr && typeof addr === 'object') {
    o = { ...addr };
  } else if (typeof addr === 'string') {
    try {
      const parsed = JSON.parse(addr);
      o = parsed && typeof parsed === 'object' ? { ...parsed } : { line1: addr };
    } catch {
      o = { line1: addr };
    }
  } else {
    o = {};
  }
  if (city && !o.city) o.city = city;
  if (country && !o.country) o.country = country;

  const addressText = [o.line1, o.line2, o.city, o.state, o.postalCode, o.country]
    .filter(Boolean).join(', ');

  return { ...o, addressText };
}

app.get('/vendor/profile', authRequired, async (req, res) => {
  try {
    const wallet = String(req.user?.address || req.user?.sub || '').toLowerCase();
    if (!wallet) return res.status(401).json({ error: 'unauthenticated' });

    // 1. [FIX] Added telegram_chat_id and telegram_username to the SQL query
    const { rows } = await pool.query(
      `SELECT wallet_address, vendor_name, email, phone, website, address,
              telegram_chat_id, telegram_username
         FROM vendor_profiles
        WHERE lower(wallet_address) = lower($1)
        LIMIT 1`,
      [wallet]
    );

    if (!rows.length) {
      // Return an empty-but-valid shape so the UI doesn't crash
      return res.json({
        walletAddress: wallet,
        vendorName: '',
        email: '',
        phone: '',
        website: '',
        address: { line1: '', city: '', postalCode: '', country: '' },
        telegram_chat_id: null,
        telegram_username: null,
      });
    }

    const r = rows[0];

    // address can be stored as string or JSON; normalize to object
    let addr = { line1: '', city: '', postalCode: '', country: '' };
    if (typeof r.address === 'string' && r.address.trim().startsWith('{')) {
      try {
        const a = JSON.parse(r.address);
        addr = {
          line1: a?.line1 || '',
          city: a?.city || '',
          postalCode: a?.postalCode || a?.postal_code || '',
          country: a?.country || ''
        };
      } catch {
        addr = { line1: r.address || '', city: '', postalCode: '', country: '' };
      }
    } else if (typeof r.address === 'string') {
      addr = { line1: r.address || '', city: '', postalCode: '', country: '' };
    }

    // 2. [FIX] Added the new fields to the JSON response
    // The frontend page checks for all these property names
    return res.json({
      walletAddress: r.wallet_address,
      vendorName: r.vendor_name || '',
      email: r.email || '',
      phone: r.phone || '',
      website: r.website || '',
      address: addr,
      telegram_chat_id: r.telegram_chat_id,
      telegramChatId: r.telegram_chat_id, // Alias for frontend
      telegram_username: r.telegram_username,
      telegramUsername: r.telegram_username // Alias for frontend
    });
  } catch (e) {
    console.error('GET /vendor/profile error:', e);
    return res.status(500).json({ error: 'failed_to_load_vendor_profile' });
  }
});

// ── PROPOSER PROFILE (Entity) — STRICTLY SEPARATE FROM VENDOR ──────────────────
app.post('/proposer/profile', requireAuth, async (req, res) => {
  try {
    const wallet = String(req.user?.address || req.user?.sub || '').toLowerCase();
    if (!wallet) return res.status(401).json({ error: 'unauthenticated' });

    // 🔒 HARD SEPARATION:
    // If this wallet is (now) a proposer, nuke any vendor profile for the same wallet.
    await pool.query('DELETE FROM vendor_profiles WHERE wallet_address = $1 AND tenant_id = $2', [wallet, req.tenantId]);

    const {
      vendorName,            // → org_name
      email,                 // → contact_email
      phone,
      website,
      address,               // object OR string
      city,
      country,
      whatsapp,
      telegram_chat_id,
      telegram_username,
    } = req.body || {};

    // Normalize website like in vendor route (prepend https:// if missing)
    const rawWebsite = (website || '').trim();
    const websiteNorm = rawWebsite && !/^https?:\/\//i.test(rawWebsite) ? `https://${rawWebsite}` : rawWebsite || null;

    // Store address: keep JSON when object; keep as text when string
    const addressVal =
      typeof address === 'string' ? (address || null)
        : (address ? JSON.stringify(address) : null);

    await pool.query(`
      INSERT INTO proposer_profiles
        (wallet_address, org_name, contact_email, phone, website, address, city, country,
         whatsapp, telegram_chat_id, telegram_username, updated_at, tenant_id)
      VALUES
        ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11, NOW(), $12)
      ON CONFLICT (wallet_address) DO UPDATE SET
        org_name          = COALESCE(NULLIF(EXCLUDED.org_name, ''),         proposer_profiles.org_name),
        contact_email     = COALESCE(NULLIF(EXCLUDED.contact_email, ''),     proposer_profiles.contact_email),
        phone             = COALESCE(NULLIF(EXCLUDED.phone, ''),             proposer_profiles.phone),
        website           = COALESCE(NULLIF(EXCLUDED.website, ''),           proposer_profiles.website),
        address           = CASE
                              WHEN EXCLUDED.address IS NULL OR EXCLUDED.address = '' THEN proposer_profiles.address
                              ELSE EXCLUDED.address
                            END,
        city              = COALESCE(NULLIF(EXCLUDED.city, ''),              proposer_profiles.city),
        country           = COALESCE(NULLIF(EXCLUDED.country, ''),           proposer_profiles.country),
        whatsapp          = COALESCE(NULLIF(EXCLUDED.whatsapp, ''),          proposer_profiles.whatsapp),
        telegram_chat_id  = COALESCE(NULLIF(EXCLUDED.telegram_chat_id, ''),  proposer_profiles.telegram_chat_id),
        telegram_username = COALESCE(NULLIF(EXCLUDED.telegram_username, ''), proposer_profiles.telegram_username),
        updated_at        = NOW()
    `, [
      wallet,
      vendorName ?? null,
      email ?? null,
      phone ?? null,
      websiteNorm,
      addressVal,
      city ?? null,
      country ?? null,
      whatsapp ?? null,
      telegram_chat_id ?? null,
      telegram_username ?? null,
      req.tenantId
    ]);

    // Minimal, consistent response (don’t leak vendor shape)
    return res.json({ ok: true, role: 'proposer' });
  } catch (e) {
    console.error('POST /proposer/profile error', e);
    return res.status(500).json({ error: 'Failed to save proposer profile' });
  }
});

// Read Entity/Proposer profile **from proposer_profiles**
app.get('/proposer/profile', requireAuth, async (req, res) => {
  try {
    const addr = String(req.user?.address || req.user?.sub || "").toLowerCase();
    const r = await pool.query(`
      SELECT org_name, contact_email, phone, website, address, city, country, telegram_username, telegram_chat_id, whatsapp
      FROM proposer_profiles
      WHERE lower(wallet_address)=lower($1) AND tenant_id=$2
      LIMIT 1
    `, [addr, req.tenantId]);

    if (!r.rows.length) return res.json({}); // empty profile

    const row = r.rows[0];
    const norm = (s) => (typeof s === 'string' && s.trim() ? s.trim() : null);

    // address may be JSON or plain text -> normalize both
    let addrObj = null, addressText = null;
    if (row.address) {
      if (typeof row.address === 'string' && row.address.trim().startsWith('{')) {
        try { addrObj = JSON.parse(row.address); } catch { }
      }
      if (addrObj && typeof addrObj === 'object') {
        const line1 = norm(addrObj.line1);
        const city = norm(addrObj.city);
        const pc = norm(addrObj.postalCode) || norm(addrObj.postal_code);
        const ctry = norm(addrObj.country);
        addressText = [line1, city, pc, ctry].filter(Boolean).join(', ') || null;
      } else {
        addressText = norm(row.address);
      }
    }

    res.json({
      vendorName: row.org_name || '',
      email: row.contact_email || '',
      phone: row.phone || '',
      website: row.website || '',
      address: addrObj || addressText || null,
      addressText,
      telegram_username: row.telegram_username ?? null,
      telegram_chat_id: row.telegram_chat_id ?? null,
      whatsapp: row.whatsapp ?? null,
    });
  } catch (e) {
    console.error('GET /proposer/profile error', e);
    res.status(500).json({ error: 'Failed to load proposer profile' });
  }
});

// Choose a role AFTER profile save (SAFE + EXCLUSIVE)
app.post("/profile/choose-role", authGuard, async (req, res) => {
  const client = await pool.connect();
  try {
    const wallet = String(req.user?.address || req.user?.sub || "").toLowerCase();
    if (!wallet) return res.status(401).json({ error: "unauthorized" });

    const roleIntent = String(req.body?.role || req.query?.role || "").trim().toLowerCase(); // 'vendor' | 'proposer' | 'admin'
    if (roleIntent !== "vendor" && roleIntent !== "proposer" && roleIntent !== "admin") {
      return res.status(400).json({ error: "role_required" });
    }

    // Seed base from user_profiles (used on first insert / fallback fields)
    const { rows: base } = await client.query(
      `SELECT display_name, email, phone, website, address, city, country,
              telegram_chat_id, whatsapp
         FROM user_profiles
        WHERE lower(wallet_address)=lower($1)`,
      [wallet]
    );
    const p = base[0] || {};
    const b = req.body || {};

    await client.query('BEGIN');

    if (roleIntent === "vendor") {
      // ---- UPSERT vendor (safe, don't wipe address JSON) ----
      await client.query(
        `INSERT INTO vendor_profiles
        (wallet_address, vendor_name, email, phone, website, address, status, created_at, updated_at, telegram_chat_id, whatsapp, tenant_id)
        VALUES
          ($1, COALESCE($2, ''), $3, $4, $5, $6, 'pending', NOW(), NOW(), $7, $8, $9)
   ON CONFLICT(wallet_address) DO UPDATE SET
    vendor_name = COALESCE(NULLIF(EXCLUDED.vendor_name, ''), vendor_profiles.vendor_name),
        email = COALESCE(EXCLUDED.email, vendor_profiles.email),
        phone = COALESCE(EXCLUDED.phone, vendor_profiles.phone),
        website = COALESCE(EXCLUDED.website, vendor_profiles.website),
        address = CASE
                          WHEN EXCLUDED.address IS NULL OR EXCLUDED.address = '' THEN vendor_profiles.address
                          ELSE EXCLUDED.address
                        END,
        telegram_chat_id = COALESCE(EXCLUDED.telegram_chat_id, vendor_profiles.telegram_chat_id),
        whatsapp = COALESCE(EXCLUDED.whatsapp, vendor_profiles.whatsapp),
        status = COALESCE(NULLIF(vendor_profiles.status, ''), 'pending'),
        updated_at = NOW()
          `,
        [
          wallet,
          (b.vendorName ?? p.display_name ?? "").trim(),
          b.email ?? p.email ?? null,
          b.phone ?? p.phone ?? null,
          b.website ?? p.website ?? null,
          typeof b.address === "string" ? b.address : (b.address ? JSON.stringify(b.address) : (p.address ?? null)),
          b.telegram_chat_id ?? p.telegram_chat_id ?? null,
          b.whatsapp ?? p.whatsapp ?? null,
          req.tenantId
        ]
      );

      // ---- EXCLUSIVITY: make proposer side inactive for this wallet ----
      await client.query(
        `UPDATE proposer_profiles
            SET status = 'inactive', updated_at = NOW()
          WHERE lower(wallet_address) = lower($1) AND tenant_id = $2`,
        [wallet, req.tenantId]
      );
    }

    if (roleIntent === "proposer") {
      // Prepare proposer fields (includes telegram_username)
      const orgName = (b.vendorName ?? b.orgName ?? p.display_name ?? "").trim();
      const email = b.email ?? p.email ?? null;
      const phone = b.phone ?? p.phone ?? null;
      const website = b.website ?? p.website ?? null;
      const city = b.city ?? p.city ?? null;
      const country = b.country ?? p.country ?? null;
      const tgChatId = b.telegram_chat_id ?? p.telegram_chat_id ?? null;
      const tgUser = b.telegram_username ?? null; // <- include username
      const whatsapp = b.whatsapp ?? p.whatsapp ?? null;
      const addressVal =
        typeof b.address === "string" ? b.address :
          (b.address ? JSON.stringify(b.address) : (p.address ?? null));

      // ---- UPSERT proposer (safe, don't wipe address JSON) ----
      await client.query(
        `INSERT INTO proposer_profiles
          (wallet_address, org_name, contact_email, phone, website, address, city, country,
           telegram_chat_id, telegram_username, whatsapp, status, created_at, updated_at, tenant_id)
        VALUES
          ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,'active',NOW(),NOW(), $12)
   ON CONFLICT (wallet_address) DO UPDATE SET
    org_name          = COALESCE(NULLIF(EXCLUDED.org_name, ''),         proposer_profiles.org_name),
    contact_email     = COALESCE(NULLIF(EXCLUDED.contact_email, ''),    proposer_profiles.contact_email),
    phone             = COALESCE(NULLIF(EXCLUDED.phone, ''),            proposer_profiles.phone),
    website           = COALESCE(NULLIF(EXCLUDED.website, ''),          proposer_profiles.website),
    address           = CASE
                          WHEN EXCLUDED.address IS NULL OR EXCLUDED.address = '' THEN proposer_profiles.address
                          ELSE EXCLUDED.address
                        END,
    city              = COALESCE(NULLIF(EXCLUDED.city, ''),             proposer_profiles.city),
    country           = COALESCE(NULLIF(EXCLUDED.country, ''),          proposer_profiles.country),
    telegram_chat_id  = COALESCE(NULLIF(EXCLUDED.telegram_chat_id, ''), proposer_profiles.telegram_chat_id),
    telegram_username = COALESCE(NULLIF(EXCLUDED.telegram_username, ''),proposer_profiles.telegram_username),
    whatsapp          = COALESCE(NULLIF(EXCLUDED.whatsapp, ''),         proposer_profiles.whatsapp),
    status            = 'active',
    updated_at        = NOW()
        `,
        [wallet, orgName, email, phone, website, addressVal, city, country, tgChatId, tgUser, whatsapp, req.tenantId]
      );

      // ---- EXCLUSIVITY: make vendor side inactive for this wallet ----
      await client.query(
        `UPDATE vendor_profiles
            SET status='inactive', updated_at=NOW()
          WHERE lower(wallet_address)=lower($1) AND tenant_id=$2`,
        [wallet, req.tenantId]
      );
    }

    await client.query('COMMIT');

    // Recompute durable roles, choose final role, issue token (unchanged)
    let roles = await durableRolesForAddress(wallet, req.tenantId);
    let role = roleFromDurableOrIntent(roles, roleIntent);
    if (isAdminAddress(wallet)) {
      roles = Array.from(new Set([...(roles || []), "admin"]));
      role = role === "vendor" || role === "proposer" ? role : "admin";
    }
    const token = signJwt({ sub: wallet, role, roles });
    res.cookie("auth_token", token, {
      httpOnly: true, secure: true, sameSite: "none", maxAge: 7 * 24 * 3600 * 1000,
    });
    return res.json({ ok: true, role, roles, token });
  } catch (e) {
    try { await client.query('ROLLBACK'); } catch { }
    console.error("POST /profile/choose-role error", e);
    return res.status(500).json({ error: "choose_role_failed" });
  } finally {
    client.release();
  }
});


// VENDOR: create/update ONLY vendor_profiles
app.post('/vendor/profile', authRequired, async (req, res) => {
  const wallet = String(req.user?.sub || '').toLowerCase();
  const { error, value } = profileSchema.validate(req.body || {}, { abortEarly: false });
  if (error) return res.status(400).json({ error: error.message });

  // normalize website
  const rawWebsite = (value.website || '').trim();
  const website = rawWebsite && !/^https?:\/\//i.test(rawWebsite) ? `https://${rawWebsite}` : rawWebsite;

  // normalize address
  let addressText = '';
  let addressJson = null;
  if (typeof value.address === 'string') {
    addressText = value.address.trim();
  } else if (value.address && typeof value.address === 'object') {
    const a = value.address;
    addressJson = {
      line1: String(a.line1 || ''),
      city: String(a.city || ''),
      postalCode: String(a.postalCode || ''),
      country: String(a.country || ''),
    };
    addressText = [addressJson.line1, addressJson.city, addressJson.postalCode, addressJson.country].filter(Boolean).join(', ');
  }
  const addressToStore = addressJson ? JSON.stringify(addressJson) : addressText;

  try {
    // 🔒 HARD EXCLUSIVITY: a wallet cannot be an entity (proposer) at the same time
    await pool.query(`DELETE FROM proposer_profiles WHERE wallet_address = $1 AND tenant_id = $2`, [wallet, req.tenantId]);

    const { rows } = await pool.query(
      `INSERT INTO vendor_profiles
         (wallet_address, vendor_name, email, phone, address, website, created_at, updated_at, tenant_id)
       VALUES
         ($1,$2,$3,$4,$5,$6, now(), now(), $7)
       ON CONFLICT (wallet_address) DO UPDATE SET
         vendor_name = EXCLUDED.vendor_name,
         email       = EXCLUDED.email,
         phone       = EXCLUDED.phone,
         address     = EXCLUDED.address,
         website     = EXCLUDED.website,
         updated_at  = now()
       RETURNING wallet_address, vendor_name, email, phone, address, website`,
      [wallet, value.vendorName || null, value.email || null, value.phone || null, addressToStore, website || null, req.tenantId]
    );

    const r = rows[0];
    let parsed = null;
    try { parsed = JSON.parse(r.address || ''); } catch { }
    const address =
      parsed && typeof parsed === 'object'
        ? { line1: parsed.line1 || '', city: parsed.city || '', country: parsed.country || '', postalCode: parsed.postalCode || parsed.postal_code || '' }
        : { line1: r.address || '', city: '', country: '', postalCode: '' };

    res.json({
      walletAddress: r.wallet_address,
      vendorName: r.vendor_name || '',
      email: r.email || '',
      phone: r.phone || '',
      website: r.website || '',
      address,
    });
  } catch (e) {
    console.error('POST /vendor/profile error:', e);
    res.status(500).json({ error: 'Failed to save profile' });
  }
});

app.post('/tg/webhook', async (req, res) => {
  try {
    const update = req.body || {};
    const from = update?.message?.from || update?.callback_query?.from || {};
    const chatObj = update?.message?.chat || update?.callback_query?.message?.chat || {};
    const chatId = chatObj?.id ?? from?.id;
    const username = from?.username || chatObj?.username || null;
    const textRaw =
      update?.message?.text ??
      update?.callback_query?.data ??
      update?.message?.caption ??
      '';
    const text = String(textRaw).trim();

    if (!chatId) return res.json({ ok: true });
    const chatIdStr = String(chatId);

    // ------------------------------------------------------------------
    // AUTO-REFRESH USERNAME
    // ------------------------------------------------------------------
    if (username) {
      // Update vendor_profiles
      await pool.query(
        `UPDATE vendor_profiles
           SET telegram_username = $1,
               updated_at = NOW()
         WHERE telegram_chat_id = $2`,
        [username, chatIdStr]
      ).catch(() => null);

      // Update proposals
      await pool.query(
        `UPDATE proposals
           SET owner_telegram_username = $1,
               updated_at = NOW()
         WHERE owner_telegram_chat_id = $2`,
        [username, chatIdStr]
      ).catch(() => null);

      // Update proposer_profiles
      await pool.query(
        `UPDATE proposer_profiles
           SET telegram_username = $1,
               updated_at = NOW()
         WHERE telegram_chat_id = $2`,
        [username, chatIdStr]
      ).catch(() => null);
    }

    if (!text) return res.json({ ok: true });

    // ------------------------------------------------------------------
    // LINK NEW WALLET
    // ------------------------------------------------------------------
    let wallet = '';
    if (/^\/link\s+/i.test(text)) {
      wallet = text.slice(6).trim();
    } else {
      const m = text.match(/^\/start\s+link_(0x[a-fA-F0-9]{40})$/);
      if (m) wallet = m[1];
    }

    if (!wallet) return res.json({ ok: true });

    if (!/^0x[a-fA-F0-9]{40}$/.test(wallet)) {
      await sendTelegram([chatIdStr], 'Send: /link 0xYourWalletAddress');
      return res.json({ ok: true });
    }

    const walletLower = wallet.toLowerCase();

    // --- Unlink this chat ID from any OTHER profiles ---

    // Clear from other vendors
    await pool.query(
      `UPDATE vendor_profiles
          SET telegram_chat_id = NULL,
              telegram_username = NULL,
              updated_at = NOW()
        WHERE telegram_chat_id = $1
          AND LOWER(wallet_address) <> LOWER($2)`,
      [chatIdStr, walletLower]
    ).catch(() => null);

    // Clear from other proposer_profiles
    await pool.query(
      `UPDATE proposer_profiles
          SET telegram_chat_id = NULL,
              telegram_username = NULL,
              updated_at = NOW()
        WHERE telegram_chat_id = $1
          AND LOWER(wallet_address) <> LOWER($2)`, // Using 'wallet_address'
      [chatIdStr, walletLower]
    ).catch(() => null);

    // --- Link this chat ID to the correct profile ---

    // ====================================================================
    // 1. [THE FIX] UPSERT (INSERT OR UPDATE) 'vendor_profiles'
    // ====================================================================
    // This will create a new row if one doesn't exist for this wallet
    await pool.query(
      `INSERT INTO vendor_profiles (
         wallet_address, 
         telegram_chat_id, 
         telegram_username, 
         created_at, 
         updated_at
       )
       VALUES ($1, $2, $3, NOW(), NOW())
       ON CONFLICT (wallet_address)
       DO UPDATE SET
         telegram_chat_id = EXCLUDED.telegram_chat_id,
         telegram_username = EXCLUDED.telegram_username,
         updated_at = NOW()`,
      [walletLower, chatIdStr, username]
    ).catch((dbErr) => {
      console.error("WEBHOOK VENDOR UPSERT FAILED:", dbErr);
    });

    // Link to proposals (This is an UPDATE, it's fine)
    await pool.query(
      `UPDATE proposals
         SET owner_telegram_chat_id = $1,
             owner_telegram_username = $2,
             updated_at = NOW()
       WHERE LOWER(owner_wallet) = LOWER($3)`,
      [chatIdStr, username, walletLower]
    ).catch(() => null);

    // ====================================================================
    // 2. [THE FIX] UPSERT (INSERT OR UPDATE) 'proposer_profiles'
    // ====================================================================
    // This will create a new row if one doesn't exist for this wallet
    await pool.query(
      `INSERT INTO proposer_profiles (
         wallet_address, 
         telegram_chat_id, 
         telegram_username, 
         created_at, 
         updated_at
       )
       VALUES ($1, $2, $3, NOW(), NOW())
       ON CONFLICT (wallet_address)
       DO UPDATE SET
         telegram_chat_id = EXCLUDED.telegram_chat_id,
         telegram_username = EXCLUDED.telegram_username,
         updated_at = NOW()`,
      [walletLower, chatIdStr, username]
    ).catch((dbErr) => {
      console.error("WEBHOOK PROPOSER UPSERT FAILED:", dbErr);
    });

    // --- Confirm to user ---
    await sendTelegram(
      [chatIdStr],
      `✅ Telegram linked to ${wallet}${username ? ` as @${username}` : ''}`
    );

    return res.json({ ok: true });
  } catch (e) {
    console.error("WEBHOOK GLOBAL ERROR:", e);
    return res.json({ ok: true });
  }
});

// ==============================
// Routes — Vendor helpers
// ==============================
app.get("/vendor/bids", async (req, res) => {
  try {
    const role = (req.user?.role || "guest").toLowerCase();
    const caller = (req.user?.sub || "").toLowerCase();

    if (role === "admin") {
      const { rows } = await pool.query("SELECT * FROM bids WHERE tenant_id=$1 ORDER BY created_at DESC NULLS LAST, bid_id DESC", [req.tenantId]);
      return res.json(mapRows(rows));
    }

    // Scope for vendors/guests; require auth when scoping is on
    if (SCOPE_BIDS_FOR_VENDOR) {
      if (!caller) return res.status(401).json({ error: "Unauthorized" });
      const { rows } = await pool.query(
        "SELECT * FROM bids WHERE lower(wallet_address)=lower($1) AND tenant_id=$2 ORDER BY created_at DESC NULLS LAST, bid_id DESC",
        [caller, req.tenantId]
      );
      return res.json(mapRows(rows));
    }

    // Flag OFF: safest default is still to scope to caller if present
    if (caller) {
      const { rows } = await pool.query(
        "SELECT * FROM bids WHERE lower(wallet_address)=lower($1) AND tenant_id=$2 ORDER BY created_at DESC NULLS LAST, bid_id DESC",
        [caller, req.tenantId]
      );
      return res.json(mapRows(rows));
    }

    // If completely unauthenticated and flag OFF, preserve legacy behavior
    const { rows } = await pool.query("SELECT * FROM bids WHERE tenant_id=$1 ORDER BY created_at DESC NULLS LAST, bid_id DESC", [req.tenantId]);
    return res.json(mapRows(rows));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get("/vendor/payments", async (_req, res) => {
  // Flatten milestones that have paymentTxHash
  try {
    const { rows } = await pool.query("SELECT * FROM bids");
    const out = [];
    for (const r of rows) {
      const milestones = Array.isArray(r.milestones) ? r.milestones : JSON.parse(r.milestones || "[]");
      milestones.forEach((m) => {
        if (m?.paymentTxHash) {
          out.push({
            success: true,
            transactionHash: m.paymentTxHash,
            amount: m.amount,
            currency: r.preferred_stablecoin,
            toAddress: r.wallet_address,
            date: m.paymentDate || null,
          });
        }
      });
    }
    res.json(out);
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

/** ADMIN: list bids (optional filter by vendor wallet)
 *  GET /admin/bids
 *  GET /admin/bids?vendorWallet=0xabc...
 *  Returns: { items, total, page, pageSize }
 */
app.get('/admin/bids', adminGuard, async (req, res) => {
  try {
    const vendorWallet = (String(req.query.vendorWallet || '').toLowerCase()) || null;
    const page = Math.max(1, parseInt(String(req.query.page ?? '1'), 10));
    const limit = Math.min(200, Math.max(1, parseInt(String(req.query.limit ?? '100'), 10)));
    const offset = (page - 1) * limit;

    const listSql = `
  SELECT
    b.bid_id,
    b.proposal_id,
    LOWER(b.wallet_address) AS vendor_wallet,
    b.vendor_name,
    b.price_usd,
    b.status,
    b.created_at,
    b.doc,
    COALESCE(b.files, '[]'::jsonb) AS files,
    COALESCE(p.title, 'Untitled Project') AS project_title
  FROM bids b
  LEFT JOIN proposals p ON p.proposal_id = b.proposal_id
  WHERE ($1::text IS NULL OR LOWER(b.wallet_address) = $1) AND b.tenant_id = $2
  ORDER BY b.created_at DESC NULLS LAST, b.bid_id DESC
  LIMIT $3 OFFSET $4
`;
    const countSql = `
      SELECT COUNT(*)::int AS cnt
      FROM bids b
      WHERE ($1::text IS NULL OR LOWER(b.wallet_address) = $1) AND b.tenant_id = $2
    `;

    const [list, count] = await Promise.all([
      pool.query(listSql, [vendorWallet, req.tenantId, limit, offset]),
      pool.query(countSql, [vendorWallet, req.tenantId]),
    ]);

    // Robust JSON coercion (handles jsonb, json text, null)
    const items = list.rows.map(r => {
      let doc = r.doc;
      if (typeof doc === 'string') { try { doc = JSON.parse(doc); } catch { } }

      let files = r.files;
      if (typeof files === 'string') { try { files = JSON.parse(files); } catch { } }
      if (!Array.isArray(files)) files = files ? [files] : [];

      return {
        id: r.bid_id,
        projectId: r.proposal_id,
        projectTitle: r.project_title,
        vendorWallet: r.vendor_wallet,
        vendorName: r.vendor_name,
        amountUSD: r.price_usd,
        status: r.status,
        createdAt: new Date(r.created_at).toISOString(),
        doc: doc || null,   // << expose doc
        files,              // << expose files[]
      };
    });

    res.json({ items, total: count.rows[0].cnt, page, pageSize: limit });
  } catch (e) {
    console.error('GET /admin/bids error', e);
    res.status(500).json({ error: 'Server error' });
  }
});

// ADMIN: proofs page requires full bids + milestones + payment state
app.get('/admin/proofs-bids', adminGuard, async (req, res) => {
  try {
    // Optional: auto-drain a few pending SAFE payments each load
    // await autoDrainPendingSafePayments(pool);

    const { rows } = await pool.query(
      `SELECT
         bid_id,
         proposal_id,
         vendor_name,
         wallet_address,
         milestones,
         price_usd,
         status,
         created_at
       FROM bids
       WHERE tenant_id = $1
       ORDER BY created_at DESC NULLS LAST, bid_id DESC`,
      [req.tenantId]
    );

    // Hydrate with Safe overlay so executed txs flip to PAID immediately
    const hydrated = await Promise.all(
      rows.map(b => overlayPaidFromMp(b, pool).catch(() => b)) // don't let one failure kill the list
    );

    // Return camelCase keys the React page expects
    const out = hydrated.map(r => ({
      bidId: Number(r.bid_id),
      proposalId: Number(r.proposal_id),
      vendorName: r.vendor_name,
      walletAddress: r.wallet_address,
      priceUsd: r.price_usd == null ? null : Number(r.price_usd),
      status: r.status ?? null,
      createdAt: r.created_at,
      milestones: Array.isArray(r.milestones)
        ? r.milestones
        : (typeof r.milestones === 'string'
          ? (() => { try { return JSON.parse(r.milestones || '[]'); } catch { return []; } })()
          : []
        ),
    }));

    // Make sure Netlify / browsers don’t cache this list
    res.set('Cache-Control', 'no-store, no-cache, must-revalidate');
    res.set('Pragma', 'no-cache');
    res.set('Expires', '0');

    return res.json(out);
  } catch (e) {
    console.error('GET /admin/proofs-bids failed', e);
    return res.status(500).json({ error: 'Failed to fetch bids for proofs' });
  }
});

// ADMIN: list proposers/entities (from proposals + fallback to proposer_profiles)
app.get('/admin/proposers', adminGuard, async (req, res) => {
  try {
    const includeArchived = ['true', '1', 'yes'].includes(String(req.query.includeArchived || '').toLowerCase());
    const qRaw = String(req.query.q || '').trim();
    const q = qRaw ? `%${qRaw}%` : null;

    const page = Math.max(1, parseInt(String(req.query.page ?? '1'), 10));
    const limit = Math.min(200, Math.max(1, parseInt(String(req.query.limit ?? '100'), 10)));
    const offset = (page - 1) * limit;

    // Build WHERE for proposals and proposer_profiles with consistent placeholder indexing
    const params = [];
    let p = 0;

    const propWhere = [];
    if (!includeArchived) propWhere.push(`status <> 'archived'`);
    if (q) {
      propWhere.push(`(org_name ILIKE $${++p} OR contact ILIKE $${p} OR owner_wallet ILIKE $${p})`);
      params.push(q);
    }
    const whereSql = propWhere.length ? `WHERE ${propWhere.join(' AND ')}` : '';

    const ppWhere = [];
    if (q) {
      ppWhere.push(`(org_name ILIKE $${++p} OR contact_email ILIKE $${p} OR wallet_address ILIKE $${p})`);
      params.push(q);
    }
    const ppWhereSql = ppWhere.length ? `WHERE ${ppWhere.join(' AND ')}` : '';

    const listSql = `
      WITH base AS (
        SELECT
          proposal_id,
          org_name,
          LOWER(org_name) AS org_key,
          contact,
          LOWER(contact)  AS contact_email,
          owner_wallet,
          owner_email,
          owner_phone,
          owner_telegram_chat_id,
          owner_telegram_username,
          amount_usd,
          status,
          created_at,
          NULLIF(BTRIM(CONCAT_WS(', ',
            NULLIF(address, ''),
            NULLIF(city, ''),
            NULLIF(country, '')
          )), '') AS addr_display,
          COALESCE(LOWER(owner_wallet), LOWER(contact), LOWER(org_name)) AS entity_key
        FROM proposals
        ${whereSql}
      ),
 grp AS (
        SELECT
          entity_key,
          MAX(org_name) FILTER (WHERE org_name IS NOT NULL AND org_name <> '') AS org_name,
          MAX(owner_wallet) FILTER (WHERE owner_wallet IS NOT NULL AND owner_wallet <> '') AS wallet_address,
          MAX(contact) FILTER (WHERE contact IS NOT NULL AND contact <> '') AS contact_email,
          MAX(owner_email) FILTER (WHERE owner_email IS NOT NULL AND owner_email <> '') AS owner_email,
          MAX(owner_phone) FILTER (WHERE owner_phone IS NOT NULL AND owner_phone <> '') AS owner_phone,
          MAX(owner_telegram_chat_id) FILTER (WHERE owner_telegram_chat_id IS NOT NULL AND owner_telegram_chat_id <> '') AS owner_telegram_chat_id,
          MAX(owner_telegram_username) FILTER (WHERE owner_telegram_username IS NOT NULL AND owner_telegram_username <> '') AS owner_telegram_username,
          
          COUNT(*) AS proposals_count,
          MAX(created_at) AS last_proposal_at,
          
          -- 1. BUDGET: Sums up approved, funded, and completed (FIX: Use LOWER(TRIM))
          COALESCE(SUM(CASE 
            WHEN LOWER(TRIM(status)) IN ('approved', 'funded', 'completed') THEN amount_usd 
            ELSE 0 
          END), 0)::numeric AS total_budget_usd,

          -- 2. COUNT: Must match the budget logic exactly (FIX: Use LOWER(TRIM))
          COUNT(*) FILTER (WHERE LOWER(TRIM(status)) IN ('approved', 'funded', 'completed'))::int AS approved_count,
          
          COUNT(*) FILTER (WHERE LOWER(TRIM(status)) = 'pending')::int  AS pending_count,
          COUNT(*) FILTER (WHERE LOWER(TRIM(status)) = 'rejected')::int AS rejected_count,
          COUNT(*) FILTER (WHERE LOWER(TRIM(status)) = 'archived')::int AS archived_count
        FROM base
        GROUP BY entity_key
      ),
      latest_addr AS (
        SELECT DISTINCT ON (entity_key)
          entity_key, addr_display
        FROM base
        WHERE addr_display IS NOT NULL
        ORDER BY entity_key, created_at DESC
      ),
      -- Fallback source: proposer_profiles (entities even with 0 proposals)
      pp AS (
        SELECT
          COALESCE(LOWER(wallet_address), LOWER(contact_email), LOWER(org_name)) AS entity_key,
          MAX(org_name) FILTER (WHERE org_name IS NOT NULL AND org_name <> '') AS org_name,
          MAX(wallet_address) FILTER (WHERE wallet_address IS NOT NULL AND wallet_address <> '') AS wallet_address,
          MAX(contact_email) FILTER (WHERE contact_email IS NOT NULL AND contact_email <> '') AS contact_email,
          NULL::text AS owner_email,
          MAX(phone) FILTER (WHERE phone IS NOT NULL AND phone <> '') AS owner_phone,
          MAX(telegram_chat_id) FILTER (WHERE telegram_chat_id IS NOT NULL AND telegram_chat_id <> '') AS owner_telegram_chat_id,
          MAX(telegram_username) FILTER (WHERE telegram_username IS NOT NULL AND telegram_username <> '') AS owner_telegram_username,
          0::bigint   AS proposals_count,
          NULL::timestamptz AS last_proposal_at,
          0::numeric  AS total_budget_usd,
          0::bigint   AS approved_count,
          0::bigint   AS pending_count,
          0::bigint   AS rejected_count,
          0::bigint   AS archived_count,
          -- address display (JSON or text) + city/country fallback
          NULLIF(BTRIM(CONCAT_WS(', ',
            COALESCE(
              CASE
                WHEN address IS NULL OR address = '' THEN NULL
                WHEN address ~ '^\\s*\\{' THEN (address::jsonb->>'line1')
                ELSE address
              END, ''
            ),
            NULLIF(city, ''),
            NULLIF(country, '')
          )), '') AS addr_display
        FROM proposer_profiles
        ${ppWhereSql}
        GROUP BY COALESCE(LOWER(wallet_address), LOWER(contact_email), LOWER(org_name))
      ),
      unioned AS (
        -- Prefer proposals aggregate when present
        SELECT g.*, la.addr_display
        FROM grp g
        LEFT JOIN latest_addr la USING (entity_key)

        UNION ALL

        SELECT
          pp.entity_key, pp.org_name, pp.wallet_address, pp.contact_email, pp.owner_email,
          pp.owner_phone, pp.owner_telegram_chat_id, pp.owner_telegram_username,
          pp.proposals_count, pp.last_proposal_at, pp.total_budget_usd,
          pp.approved_count, pp.pending_count, pp.rejected_count, pp.archived_count,
          pp.addr_display
        FROM pp
        WHERE NOT EXISTS (SELECT 1 FROM grp WHERE grp.entity_key = pp.entity_key)
      )
      SELECT *
      FROM unioned
      ORDER BY last_proposal_at DESC NULLS LAST, org_name ASC
      LIMIT $${++p} OFFSET $${++p};
    `;
    const listParams = params.concat([limit, offset]);

    const countSql = `
      WITH base AS (
        SELECT
          COALESCE(LOWER(owner_wallet), LOWER(contact), LOWER(org_name)) AS entity_key
        FROM proposals
        ${whereSql}
      ),
      grp AS (
        SELECT DISTINCT entity_key FROM base
      ),
      pp_keys AS (
        SELECT DISTINCT
          COALESCE(LOWER(wallet_address), LOWER(contact_email), LOWER(org_name)) AS entity_key
        FROM proposer_profiles
        ${ppWhereSql}
      ),
      union_keys AS (
        SELECT entity_key FROM grp
        UNION
        SELECT entity_key FROM pp_keys
      )
      SELECT COUNT(*)::int AS cnt FROM union_keys;
    `;
    const countParams = params.slice();

    const [list, count] = await Promise.all([
      pool.query(listSql, listParams),
      pool.query(countSql, countParams),
    ]);

    const items = list.rows.map(r => ({
      id: r.entity_key,
      orgName: r.org_name || '',
      address: r.addr_display || null,
      walletAddress: r.wallet_address || null,
      contactEmail: r.contact_email || null,
      ownerEmail: r.owner_email || null,

      ownerPhone: r.owner_phone || null,
      ownerTelegramChatId: r.owner_telegram_chat_id || null,
      ownerTelegramUsername: r.owner_telegram_username || null,

      proposalsCount: Number(r.proposals_count) || 0,
      totalBudgetUSD: Number(r.total_budget_usd) || 0,
      lastProposalAt: r.last_proposal_at ? new Date(r.last_proposal_at).toISOString() : null,
      statusCounts: {
        approved: Number(r.approved_count) || 0,
        pending: Number(r.pending_count) || 0,
        rejected: Number(r.rejected_count) || 0,
        archived: Number(r.archived_count) || 0,
      },
    }));

    res.json({ items, total: count.rows[0].cnt, page, pageSize: limit });
  } catch (e) {
    console.error('GET /admin/proposers error', e);
    res.status(500).json({ error: 'Failed to list proposers' });
  }
});

app.post('/admin/vendors/:wallet/archive', adminGuard, async (req, res) => {
  try {
    const wallet = String(req.params.wallet || '').toLowerCase();
    if (!wallet) return res.status(400).json({ error: 'wallet required' });

    // Ensure a row exists, then set archived=true
    const { rows } = await pool.query(
      `INSERT INTO vendor_profiles (wallet_address, vendor_name, archived, created_at, updated_at, tenant_id)
         VALUES ($1, '', true, now(), now(), $2)
       ON CONFLICT (wallet_address) DO UPDATE SET
         archived = true,
         updated_at = now()
       RETURNING wallet_address, vendor_name, archived, updated_at`,
      [wallet, req.tenantId]
    );

    res.json({ ok: true, walletAddress: rows[0].wallet_address, archived: rows[0].archived });
  } catch (e) {
    console.error('POST /admin/vendors/:wallet/archive error', e);
    res.status(500).json({ error: 'Failed to archive vendor' });
  }
});

// Unarchive a vendor (admin)
app.post('/admin/vendors/:wallet/unarchive', adminGuard, async (req, res) => {
  try {
    const wallet = String(req.params.wallet || '').toLowerCase();
    if (!wallet) return res.status(400).json({ error: 'wallet required' });
    const { rows } = await pool.query(
      `UPDATE vendor_profiles
         SET archived=false, updated_at=now()
       WHERE lower(wallet_address)=lower($1) AND tenant_id=$2
       RETURNING wallet_address, archived`,
      [wallet, req.tenantId]
    );
    if (!rows.length) return res.status(404).json({ error: 'Vendor profile not found' });
    res.json({ ok: true, walletAddress: rows[0].wallet_address, archived: rows[0].archived });
  } catch (e) {
    console.error('POST /admin/vendors/:wallet/unarchive error', e);
    res.status(500).json({ error: 'Failed to unarchive vendor' });
  }
});

// Approve a vendor (admin)
app.post('/admin/vendors/:wallet/approve', adminGuard, async (req, res) => {
  try {
    const wallet = String(req.params.wallet || '').toLowerCase();
    if (!wallet) return res.status(400).json({ error: 'wallet required' });

    // ✅ UPSERT so a profile row is created if it doesn't exist
    const { rows } = await pool.query(
      `INSERT INTO vendor_profiles (wallet_address, status, updated_at, tenant_id)
         VALUES ($1, 'approved', now(), $2)
       ON CONFLICT (wallet_address) DO UPDATE SET
         status='approved',
         updated_at=now()
       RETURNING wallet_address, vendor_name, email, phone, telegram_chat_id, status`,
      [wallet, req.tenantId]
    );

    const v = rows[0];

    // notify vendor (optional, fire-and-forget)
    const walletStr = String(v.wallet_address || '');
    const msg = `✅ Your LithiumX vendor account has been approved.
✅ Tu cuenta de proveedor de LithiumX ha sido aprobada.
Wallet / Cartera: ${walletStr}`;

    Promise.allSettled([
      v.telegram_chat_id ? sendTelegram([String(v.telegram_chat_id)], msg) : null,
      v.email
        ? (async () => {
          const subject = 'Vendor account approved · Cuenta de proveedor aprobada';
          const { text, html } = bi(msg, msg);
          await sendEmail([v.email], subject, text, html);
        })()
        : null,
    ]).catch(() => null);

    res.json({ ok: true, walletAddress: v.wallet_address, status: v.status });
  } catch (e) {
    console.error('POST /admin/vendors/:wallet/approve error', e);
    res.status(500).json({ error: 'Failed to approve vendor' });
  }
});

// Reject a vendor (admin)
app.post('/admin/vendors/:wallet/reject', adminGuard, async (req, res) => {
  try {
    const wallet = String(req.params.wallet || '').toLowerCase();
    if (!wallet) return res.status(400).json({ error: 'wallet required' });

    const reason = String(req.body?.reason || '').trim() || null;

    // ✅ UPSERT so a profile row is created if it doesn't exist
    const { rows } = await pool.query(
      `INSERT INTO vendor_profiles (wallet_address, status, updated_at, tenant_id)
         VALUES ($1, 'rejected', now(), $2)
       ON CONFLICT (wallet_address) DO UPDATE SET
         status='rejected',
         updated_at=now()
       RETURNING wallet_address, vendor_name, email, phone, telegram_chat_id, status`,
      [wallet, req.tenantId]
    );

    const v = rows[0];

    // notify vendor (optional, fire-and-forget)
    const msg = `❌ Your LithiumX vendor account was not approved.${reason ? `\nReason: ${reason}` : ''}\nWallet: ${v.wallet_address}`;
    Promise.allSettled([
      v.telegram_chat_id ? sendTelegram([String(v.telegram_chat_id)], msg) : null,
      v.email ? (async () => {
        const { text, html } = bi(msg, msg);
        await sendEmail([v.email], 'Vendor account not approved', text, html);
      })() : null,
    ]).catch(() => null);

    res.json({ ok: true, walletAddress: v.wallet_address, status: v.status });
  } catch (e) {
    console.error('POST /admin/vendors/:wallet/reject error', e);
    res.status(500).json({ error: 'Failed to reject vendor' });
  }
});

/** ADMIN: Delete a vendor profile by wallet (bids remain) */
app.delete('/admin/vendors/:wallet', adminGuard, async (req, res) => {
  try {
    const wallet = String(req.params.wallet || '').toLowerCase();
    if (!wallet) return res.status(400).json({ error: 'wallet required' });

    const { rowCount } = await pool.query(
      `DELETE FROM vendor_profiles WHERE lower(wallet_address) = $1 AND tenant_id = $2`,
      [wallet, req.tenantId]
    );
    if (rowCount === 0) return res.status(404).json({ error: 'Vendor profile not found' });

    res.json({ success: true });
  } catch (e) {
    console.error('DELETE /admin/vendors/:wallet error', e);
    res.status(500).json({ error: 'Failed to delete vendor' });
  }
});

// /admin/vendors — normalized vendor list (profiles + bids)
app.get('/admin/vendors', adminGuard, async (req, res) => {
  try {
    const includeArchived = ['true', '1', 'yes'].includes(String(req.query.includeArchived || '').toLowerCase());

    const sqlCore = `
      WITH a AS (
        SELECT
          LOWER(b.wallet_address)                                            AS wallet_address,
          COUNT(*)::int                                                      AS bids_count,
          MAX(b.created_at)                                                  AS last_bid_at,
          COALESCE(SUM(CASE WHEN b.status IN ('approved','completed')
                            THEN b.price_usd ELSE 0 END),0)::numeric         AS total_awarded_usd,
          MAX(NULLIF(b.vendor_name, ''))                                     AS bid_vendor_name
        FROM bids b
        WHERE b.tenant_id = $1
        GROUP BY LOWER(b.wallet_address)
      ),
      vp AS (
        SELECT DISTINCT ON (LOWER(wallet_address))
               LOWER(wallet_address) AS wallet_address,
               vendor_name,
               email,
               phone,
               website,
               address,
               telegram_username,
               telegram_chat_id,
               whatsapp,
               COALESCE(archived,false)        AS archived,
               COALESCE(status,'pending')      AS status,
               COALESCE(kyc_status,'none')     AS kyc_status
        FROM vendor_profiles
        WHERE tenant_id = $1
        ORDER BY
          LOWER(wallet_address),
          (NULLIF(vendor_name, '') IS NULL),                  -- prefer non-empty vendor_name
          COALESCE(updated_at, created_at) DESC NULLS LAST    -- newest wins
      )
      SELECT
        COALESCE(NULLIF(vp.vendor_name,''), NULLIF(a.bid_vendor_name,''), '') AS vendor_name,
        COALESCE(vp.wallet_address, a.wallet_address)                         AS wallet_address,
        COALESCE(a.bids_count, 0)                                            AS bids_count,
        a.last_bid_at,
        COALESCE(a.total_awarded_usd, 0)                                     AS total_awarded_usd,
        vp.vendor_name                                                        AS profile_vendor_name,
        vp.email,
        vp.phone,
        vp.website,
        vp.address                                                            AS address_raw,
        vp.telegram_username,
        vp.telegram_chat_id,
        vp.whatsapp,
        COALESCE(vp.archived,false)                                          AS archived,
        COALESCE(vp.status,'pending')                                        AS status,
        COALESCE(vp.kyc_status,'none')                                       AS kyc_status
      FROM a
      FULL OUTER JOIN vp ON vp.wallet_address = a.wallet_address
    `;

    let sql = `SELECT * FROM (${sqlCore}) s`;
    if (!includeArchived) {
      sql += ` WHERE COALESCE(s.archived,false) = false`;
    }
    sql += ` ORDER BY s.last_bid_at DESC NULLS LAST, s.vendor_name ASC`;

    const { rows } = await pool.query(sql, [req.tenantId]);

    const norm = (s) => (typeof s === 'string' && s.trim() !== '' ? s.trim() : null);

    const out = rows.map((r) => {
      // Parse address_raw -> addrObj (supports jsonb or stringified JSON)
      let addrObj = null;
      const raw = r.address_raw;
      if (raw && typeof raw === 'object') {
        addrObj = raw;
      } else if (typeof raw === 'string' && raw.trim().startsWith('{')) {
        try { addrObj = JSON.parse(raw.trim()); } catch { }
      }

      // Build normalized address object + string
      const parts = addrObj && typeof addrObj === 'object'
        ? {
          line1: norm(addrObj.line1),
          city: norm(addrObj.city),
          state: norm(addrObj.state),
          postalCode: norm(addrObj.postalCode) || norm(addrObj.postal_code),
          country: norm(addrObj.country),
        }
        : {
          line1: norm(raw),
          city: null,
          state: null,
          postalCode: null,
          country: null,
        };

      const addressText = [parts.line1, parts.city, parts.postalCode, parts.country]
        .filter(Boolean).join(', ') || null;

      const email = norm(r.email);
      const phone = norm(r.phone);
      const website = norm(r.website);
      const tgId = norm(r.telegram_chat_id);
      const tgUser = norm(r.telegram_username);
      const whatsapp = norm(r.whatsapp);

      return {
        // core
        vendorName: r.profile_vendor_name || r.vendor_name || '',
        walletAddress: r.wallet_address || '',
        bidsCount: Number(r.bids_count) || 0,
        lastBidAt: r.last_bid_at || null,
        totalAwardedUSD: Number(r.total_awarded_usd) || 0,

        // server-truth flags used by the UI
        status: r.status || 'pending',
        kycStatus: r.kyc_status || 'none',

        // contact
        email,
        phone,
        website,

        // explicit boolean for existing UIs
        telegramConnected: !!(tgId || tgUser || whatsapp),
        telegramChatId: tgId,
        telegramUsername: tgUser,
        whatsapp,

        // back-compat: string address for existing tables/cells
        address: addressText,
        addressText,
        // structured copy for new UI
        addressObj: {
          line1: parts.line1,
          city: parts.city,
          state: parts.state,
          postalCode: parts.postalCode,
          country: parts.country,
          addressText,
        },

        // legacy aliases some components might read
        street: parts.line1 || null,
        address1: parts.line1 || addressText,
        addressLine1: parts.line1 || addressText,
        city: parts.city,
        state: parts.state,
        postalCode: parts.postalCode,
        country: parts.country,

        // nested copies for components that deref profile.*
        profile: {
          companyName: r.profile_vendor_name ?? (r.vendor_name || null),
          contactName: null,
          email,
          contactEmail: email,
          phone,
          website,
          telegram_chat_id: tgId,
          telegram_username: tgUser,
          whatsapp,
          address: addressText,
          addressText,
          addressObj: {
            line1: parts.line1,
            city: parts.city,
            state: parts.state,
            postalCode: parts.postalCode,
            country: parts.country,
            addressText,
          },
          street: parts.line1 || null,
          address1: parts.line1 || addressText,
          address2: null,
          city: parts.city,
          state: parts.state,
          postalCode: parts.postalCode,
          country: parts.country,
          notes: null,
        },

        archived: !!r.archived,
      };
    });

    // Hide admin wallets from the list
    const outFiltered = out.filter(v => {
      const w = String(v.walletAddress || '').toLowerCase();
      return w && !isAdminAddress(w);
    });

    res.json(outFiltered);
  } catch (e) {
    console.error('GET /admin/vendors error', e);
    res.status(500).json({ error: 'Failed to list vendors' });
  }
});

// Try to find your pg client; change to match your variable if needed.
const __pool =
  (typeof pool !== 'undefined' && pool) ||
  (typeof db !== 'undefined' && db) ||
  (typeof pgPool !== 'undefined' && pgPool) ||
  null;

// ---- /admin/oversight/* routes (admin only) — FIXED ----

// SUMMARY
app.get('/admin/oversight/summary', adminGuard, async (req, res) => {
  try {
    const [proofs, payouts, p50, rev] = await Promise.all([
      pool.query(`
        SELECT
          COUNT(*) FILTER (WHERE status='pending') AS open_pending,
          COUNT(*) FILTER (WHERE status='pending'
            AND submitted_at < NOW() - INTERVAL '48 hours') AS breaching
        FROM proofs
        WHERE tenant_id = $1
      `, [req.tenantId]).catch(() => ({ rows: [{ open_pending: 0, breaching: 0 }] })),
      pool.query(`
        SELECT COUNT(*) AS cnt, COALESCE(SUM(amount_usd),0) AS usd
        FROM milestone_payments mp
        JOIN bids b ON b.bid_id = mp.bid_id
        WHERE mp.status='pending' AND b.tenant_id = $1
      `, [req.tenantId]).catch(() => ({ rows: [{ cnt: 0, usd: 0 }] })),
      pool.query(`
        SELECT PERCENTILE_CONT(0.5) WITHIN GROUP (
          ORDER BY EXTRACT(EPOCH FROM (updated_at - submitted_at))/3600.0
        ) AS p50h
        FROM proofs
        WHERE status='approved' AND submitted_at IS NOT NULL AND updated_at IS NOT NULL AND tenant_id = $1
      `, [req.tenantId]).catch(() => ({ rows: [{ p50h: 0 }] })),
      pool.query(`
        SELECT 
          COUNT(*) FILTER (WHERE status IN ('approved','rejected')) AS decided,
          COUNT(*) FILTER (WHERE status='rejected') AS rej
        FROM proofs
        WHERE tenant_id = $1
      `, [req.tenantId]).catch(() => ({ rows: [{ decided: 0, rej: 0 }] })),
    ]);

    res.json({
      openProofs: Number(proofs.rows[0].open_pending || 0),
      breachingSla: Number(proofs.rows[0].breaching || 0),
      pendingPayouts: {
        count: Number(payouts.rows[0].cnt || 0),
        totalUSD: Number(payouts.rows[0].usd || 0),
      },
      p50CycleHours: Number(p50.rows[0].p50h || 0),
      revisionRatePct: (Number(rev.rows[0].decided || 0)
        ? Math.round(100 * Number(rev.rows[0].rej) / Number(rev.rows[0].decided))
        : 0),
    });
  } catch (e) {
    console.error('oversight/summary error', e);
    res.status(500).json({ error: 'summary_failed' });
  }
});

// QUEUE
app.get('/admin/oversight/queue', adminGuard, async (req, res) => {
  try {
    const { rows } = await pool.query(`
      SELECT p.proof_id, p.bid_id, p.milestone_index, p.status,
             p.submitted_at, p.updated_at,
             b.vendor_name, b.wallet_address, b.proposal_id,
             pr.title AS project
        FROM proofs p
        JOIN bids b       ON b.bid_id = p.bid_id
        JOIN proposals pr ON pr.proposal_id = b.proposal_id
       WHERE p.status='pending' AND b.tenant_id = $1
       ORDER BY p.submitted_at NULLS LAST, p.updated_at NULLS LAST
       LIMIT 100
    `, [req.tenantId]);
    res.json(rows.map(r => ({
      id: r.proof_id,                       // ← no “id” column, use proof_id
      vendor: r.vendor_name || r.wallet_address,
      project: r.project,
      milestone: Number(r.milestone_index) + 1,
      ageHours: r.submitted_at
        ? Math.max(0, (Date.now() - new Date(r.submitted_at).getTime()) / 3600000)
        : null,
      status: r.status,
      risk: (r.submitted_at && (Date.now() - new Date(r.submitted_at).getTime()) > 48 * 3600000) ? 'sla' : null,
      actions: { bidId: r.bid_id, proposalId: r.proposal_id },
    })));
  } catch (e) {
    console.error('oversight/queue error', e);
    res.status(500).json({ error: 'queue_failed' });
  }
});

// VENDORS
app.get('/admin/oversight/vendors', adminGuard, async (req, res) => {
  try {
    const { rows } = await pool.query(`
      SELECT
        b.vendor_name,
        b.wallet_address,
        COUNT(p.proof_id)                                 AS proofs,
        COUNT(p.proof_id) FILTER (WHERE p.status='approved') AS approved,
        COUNT(p.proof_id) FILTER (WHERE p.status='rejected') AS cr,
        COUNT(DISTINCT b.bid_id)                          AS bids,
        MAX(p.updated_at)                                 AS last_activity
      FROM bids b
      LEFT JOIN proofs p ON p.bid_id = b.bid_id
      WHERE b.tenant_id = $1
      GROUP BY b.vendor_name, b.wallet_address
      ORDER BY proofs DESC NULLS LAST, vendor_name ASC
      LIMIT 200
    `, [req.tenantId]);
    res.json(rows.map(r => ({
      vendor: r.vendor_name || '(unnamed)',
      wallet: r.wallet_address,
      proofs: Number(r.proofs || 0),
      approved: Number(r.approved || 0),
      cr: Number(r.cr || 0),
      approvalPct: Number(r.proofs || 0)
        ? Math.round(100 * Number(r.approved || 0) / Number(r.proofs || 0))
        : 0,
      bids: Number(r.bids || 0),
      lastActivity: r.last_activity
    })));
  } catch (e) {
    console.error('oversight/vendors error', e);
    res.status(500).json({ error: 'vendors_failed' });
  }
});

// PAYOUTS
app.get('/admin/oversight/payouts', adminGuard, async (req, res) => {
  try {
    const [pend, rec] = await Promise.all([
      pool.query(`
        SELECT mp.id, mp.bid_id, mp.milestone_index, mp.amount_usd, mp.created_at
          FROM milestone_payments mp
          JOIN bids b ON b.bid_id = mp.bid_id
         WHERE mp.status='pending' AND b.tenant_id = $1
         ORDER BY mp.created_at DESC
         LIMIT 50
      `, [req.tenantId]).catch(() => ({ rows: [] })),
      pool.query(`
        SELECT mp.id, mp.bid_id, mp.milestone_index, mp.amount_usd, mp.released_at, mp.tx_hash
          FROM milestone_payments mp
          JOIN bids b ON b.bid_id = mp.bid_id
         WHERE mp.status='released' AND b.tenant_id = $1
         ORDER BY mp.released_at DESC
         LIMIT 50
      `, [req.tenantId]).catch(() => ({ rows: [] })),
    ]);
    res.json({ pending: pend.rows, recent: rec.rows });
  } catch (e) {
    console.error('oversight/payouts error', e);
    res.status(500).json({ error: 'payouts_failed' });
  }
});

// ==============================
// Admin — what's new feed (proposals, bids, proofs, decisions, payments)
// ==============================
app.get('/admin/whats-new', adminGuard, async (req, res) => {
  try {
    const since = req.query.since ? new Date(String(req.query.since)) : null;
    const hasSince = since && !Number.isNaN(since.getTime());
    const limit = Math.min(Math.max(parseInt(String(req.query.limit || '50'), 10), 1), 200);

    const params = [req.tenantId];
    if (hasSince) params.push(since.toISOString());
    params.push(limit);

    const where = hasSince ? 'WHERE ts > $2' : '';
    const limPos = hasSince ? 3 : 2;

    const sql = `
      WITH events AS (
        -- Proposals created
        SELECT p.created_at AS ts, 'proposal_submitted' AS type,
               p.proposal_id, NULL::bigint AS bid_id, NULL::int AS milestone_index,
               p.owner_wallet AS actor_wallet,
               p.title AS title, NULL::text AS vendor_name,
               p.amount_usd AS amount_usd, NULL::numeric AS price_usd, p.status AS status
          FROM proposals p

        UNION ALL
        -- Bids submitted
        SELECT b.created_at AS ts, 'bid_submitted' AS type,
               b.proposal_id, b.bid_id, NULL::int,
               b.wallet_address, NULL::text,
               b.vendor_name, NULL::numeric, b.price_usd, b.status
          FROM bids b

        UNION ALL
        -- Proofs submitted
        SELECT COALESCE(pr.submitted_at, pr.created_at) AS ts, 'proof_submitted' AS type,
               b.proposal_id, pr.bid_id, pr.milestone_index,
               b.wallet_address, NULL::text, NULL::text,
               NULL::numeric, NULL::numeric, pr.status
          FROM proofs pr
          JOIN bids b ON b.bid_id = pr.bid_id

        UNION ALL
        -- Proof decisions (approved/rejected)
        SELECT pr.updated_at AS ts, 'proof_decision' AS type,
               b.proposal_id, pr.bid_id, pr.milestone_index,
               NULL::text, NULL::text, NULL::text,
               NULL::numeric, NULL::numeric, pr.status
          FROM proofs pr
          JOIN bids b ON b.bid_id = pr.bid_id
         WHERE pr.status IN ('approved','rejected') AND b.tenant_id = $1

        UNION ALL
        -- Payments released
        SELECT mp.released_at AS ts, 'payment_released' AS type,
               b.proposal_id, mp.bid_id, mp.milestone_index,
               NULL::text, NULL::text, NULL::text,
               mp.amount_usd, NULL::numeric, 'released'
          FROM milestone_payments mp
          JOIN bids b ON b.bid_id = mp.bid_id
         WHERE mp.released_at IS NOT NULL AND b.tenant_id = $1
      )
      SELECT *
        FROM events
       ${where}
       ORDER BY ts DESC NULLS LAST
       LIMIT $${limPos};
    `;

    const { rows } = await pool.query(sql, params);
    res.json({ items: rows });
  } catch (e) {
    console.error('GET /admin/whats-new failed', e);
    res.status(500).json({ error: 'Failed to build feed' });
  }
});

// ==============================
// Vendor — what's new (scoped to my wallet)
// ==============================
app.get('/me/whats-new', authRequired, async (req, res) => {
  try {
    const me = String(req.user?.sub || '').toLowerCase();
    if (!me) return res.status(401).json({ error: 'unauthorized' });

    const since = req.query.since ? new Date(String(req.query.since)) : null;
    const hasSince = since && !Number.isNaN(since.getTime());
    const limit = Math.min(Math.max(parseInt(String(req.query.limit || '50'), 10), 1), 200);

    const params = [me, req.tenantId];
    if (hasSince) params.push(since.toISOString());
    params.push(limit);

    const where = hasSince ? 'WHERE ts > $3' : '';
    const limPos = hasSince ? 4 : 3;

    const sql = `
      WITH events AS (
        -- Proposals I bid on
        SELECT p.created_at AS ts, 'proposal_submitted' AS type,
               p.proposal_id, NULL::bigint AS bid_id, NULL::int AS milestone_index,
               p.owner_wallet AS actor_wallet,
               p.title AS title, NULL::text AS vendor_name,
               p.amount_usd AS amount_usd, NULL::numeric AS price_usd, p.status AS status
          FROM proposals p
          JOIN bids b ON b.proposal_id = p.proposal_id
         WHERE lower(b.wallet_address) = lower($1) AND b.tenant_id = $2

        UNION ALL
        -- Proposals I own (if any)
        SELECT p.created_at AS ts, 'proposal_submitted' AS type,
               p.proposal_id, NULL::bigint AS bid_id, NULL::int AS milestone_index,
               p.owner_wallet AS actor_wallet,
               p.title AS title, NULL::text AS vendor_name,
               p.amount_usd AS amount_usd, NULL::numeric AS price_usd, p.status AS status
          FROM proposals p
         WHERE lower(p.owner_wallet) = lower($1) AND p.tenant_id = $2

        UNION ALL
        -- My bids
        SELECT b.created_at AS ts, 'bid_submitted' AS type,
               b.proposal_id, b.bid_id, NULL::int,
               b.wallet_address, NULL::text,
               b.vendor_name, NULL::numeric, b.price_usd, b.status
          FROM bids b
         WHERE lower(b.wallet_address) = lower($1) AND b.tenant_id = $2

        UNION ALL
        -- My proofs
        SELECT COALESCE(pr.submitted_at, pr.created_at) AS ts, 'proof_submitted' AS type,
               b.proposal_id, pr.bid_id, pr.milestone_index,
               b.wallet_address, NULL::text, NULL::text,
               NULL::numeric, NULL::numeric, pr.status
          FROM proofs pr
          JOIN bids b ON b.bid_id = pr.bid_id
         WHERE lower(b.wallet_address) = lower($1) AND b.tenant_id = $2

        UNION ALL
        -- Decisions on my proofs
        SELECT pr.updated_at AS ts, 'proof_decision' AS type,
               b.proposal_id, pr.bid_id, pr.milestone_index,
               NULL::text, NULL::text, NULL::text,
               NULL::numeric, NULL::numeric, pr.status
          FROM proofs pr
          JOIN bids b ON b.bid_id = pr.bid_id
         WHERE lower(b.wallet_address) = lower($1) AND b.tenant_id = $2
           AND pr.status IN ('approved','rejected')

        UNION ALL
        -- Payments released to my milestones
        SELECT mp.released_at AS ts, 'payment_released' AS type,
               b.proposal_id, mp.bid_id, mp.milestone_index,
               NULL::text, NULL::text, NULL::text,
               mp.amount_usd, NULL::numeric, 'released'
          FROM milestone_payments mp
          JOIN bids b ON b.bid_id = mp.bid_id
         WHERE lower(b.wallet_address) = lower($1) AND b.tenant_id = $2
           AND mp.released_at IS NOT NULL
      )
      SELECT *
        FROM events
       ${where}
       ORDER BY ts DESC NULLS LAST
       LIMIT $${limPos};
    `;

    const { rows } = await pool.query(sql, params);
    res.json({ items: rows });
  } catch (e) {
    console.error('GET /me/whats-new failed', e);
    res.status(500).json({ error: 'Failed to build feed' });
  }
});

// Alias for legacy widget path
app.get('/agent/digest', authRequired, (req, res) => {
  const role = String(req.user?.role || '').toLowerCase();
  const target = role === 'admin' ? '/admin/whats-new' : '/me/whats-new';

  // Preserve query params like ?since=...&limit=...
  const qs = new URLSearchParams();
  if (req.query.since) qs.set('since', String(req.query.since));
  if (req.query.limit) qs.set('limit', String(req.query.limit));

  res.redirect(307, `${target}${qs.toString() ? `?${qs.toString()}` : ''}`);
});

// ==============================
// Vendor — persist/read "last seen" for the widget
// ==============================
app.get('/me/dashboard/last-seen', authRequired, async (req, res) => {
  const me = String(req.user?.sub || '').toLowerCase();
  if (!me) return res.status(401).json({ error: 'unauthorized' });
  const { rows } = await pool.query(
    `SELECT last_seen_digest FROM user_dashboard_state WHERE lower(wallet_address)=lower($1) AND tenant_id=$2 LIMIT 1`,
    [me, req.tenantId]
  );
  res.json({ lastSeen: rows[0]?.last_seen_digest || null });
});

app.post('/me/dashboard/last-seen', authRequired, async (req, res) => {
  const me = String(req.user?.sub || '').toLowerCase();
  if (!me) return res.status(401).json({ error: 'unauthorized' });
  const t = req.body?.timestamp ? new Date(String(req.body.timestamp)) : new Date();
  if (Number.isNaN(t.getTime())) return res.status(400).json({ error: 'invalid timestamp' });

  await pool.query(
    `INSERT INTO user_dashboard_state (wallet_address, last_seen_digest, updated_at, tenant_id)
     VALUES ($1, $2, now(), $3)
     ON CONFLICT (wallet_address, tenant_id) DO UPDATE
       SET last_seen_digest = EXCLUDED.last_seen_digest, updated_at = now()`,
    [me, t.toISOString(), req.tenantId]
  );
  res.json({ ok: true, lastSeen: t.toISOString() });
});

// ==============================
// Projects Directory (list with aggregates)
// ==============================
app.get("/projects", requireApprovedVendorOrAdmin, async (req, res) => {
  try {
    // Pagination / filters / sorting
    const page = Math.max(parseInt(req.query.page || '1', 10), 1);
    const pageSize = Math.min(Math.max(parseInt(req.query.pageSize || '20', 10), 1), 100);
    const offset = (page - 1) * pageSize;

    const q = String(req.query.q || '').trim().toLowerCase();
    const statuses = String(req.query.status || '')
      .split(',').map(s => s.trim()).filter(Boolean);
    const ownerWallet = String(req.query.ownerWallet || '').trim().toLowerCase();
    const vendorWallet = String(req.query.vendorWallet || '').trim().toLowerCase();
    const mineOnly = String(req.query.mineOnly || '') === 'true';
    const sort = String(req.query.sort || 'activity');

    // Current user (compatible with your JWT attach)  // :contentReference[oaicite:3]{index=3}
    const user = req.user || null;
    const isAdmin = String(user?.role || '').toLowerCase() === 'admin';
    const myWallet = String(user?.sub || '').toLowerCase();

    // Require admin OR approved vendor
    if (!isAdmin) {
      if (!myWallet) return res.status(401).json({ error: 'login_required' });
      const { rows: st } = await pool.query(
        `SELECT status FROM vendor_profiles WHERE lower(wallet_address)=lower($1) LIMIT 1`,
        [myWallet]
      );
      const status = (st[0]?.status || 'pending').toLowerCase();
      if (status !== 'approved') {
        return res.status(403).json({ error: 'vendor_not_approved' });
      }
    }

    const where = [];
    const params = [];

    if (statuses.length) {
      params.push(statuses);
      where.push(`p.status = ANY($${params.length})`);
    }
    if (q) {
      params.push(`%${q}%`);
      where.push(`(LOWER(p.title) LIKE $${params.length} OR CAST(p.proposal_id AS TEXT) LIKE $${params.length})`);
    }
    if (ownerWallet || (mineOnly && myWallet)) {
      params.push(ownerWallet || myWallet);
      where.push(`LOWER(p.owner_wallet) = $${params.length}`);
    }
    if (vendorWallet) {
      params.push(vendorWallet);
      where.push(`EXISTS (SELECT 1 FROM bids b2 WHERE b2.proposal_id = p.proposal_id AND LOWER(b2.wallet_address) = $${params.length})`);
    }
    // Non-admin default: show my proposals if no other filter
    if (!isAdmin && !ownerWallet && !mineOnly && !vendorWallet) {
      params.push(myWallet || '__no_wallet__');
      where.push(`LOWER(p.owner_wallet) = $${params.length}`);
    }

    const whereSql = where.length ? `WHERE ${where.join(' AND ')}` : '';

    const sortSql = {
      latest: 'p.created_at DESC',
      oldest: 'p.created_at ASC',
      bids: 'agg_bids_total DESC NULLS LAST',
      paid: 'agg_ms_paid DESC NULLS LAST',
      activity: 'last_activity_at DESC NULLS LAST',
    }[sort] || 'last_activity_at DESC NULLS LAST';

    // Count
    const { rows: [{ cnt }] } = await pool.query(
      `SELECT COUNT(*)::int AS cnt FROM proposals p ${whereSql}`,
      params
    );

    // List with aggregates (no new tables, use your existing schema)
    const sql = `
      SELECT
        p.proposal_id AS id,
        p.title,
        p.status,
        p.owner_wallet,
        p.owner_email,
        p.created_at,
        p.updated_at,

        -- Bids aggregates
        (SELECT COUNT(*) FROM bids b WHERE b.proposal_id = p.proposal_id) AS agg_bids_total,
        (SELECT COUNT(*) FROM bids b WHERE b.proposal_id = p.proposal_id AND b.status = 'approved') AS agg_bids_approved,

        -- Milestones: total from JSON arrays; completed if completed=true OR paymentTxHash present
        COALESCE((
          SELECT SUM(jsonb_array_length(COALESCE(b.milestones, '[]'::jsonb)))
            FROM bids b
           WHERE b.proposal_id = p.proposal_id
        ), 0) AS agg_ms_total,

        COALESCE((
          SELECT COUNT(*)
            FROM bids b
            CROSS JOIN LATERAL jsonb_array_elements(COALESCE(b.milestones, '[]'::jsonb)) ms
           WHERE b.proposal_id = p.proposal_id
             AND (
               (ms->>'completed')::boolean IS TRUE OR
               NULLIF(ms->>'paymentTxHash','') IS NOT NULL
             )
        ), 0) AS agg_ms_completed,

        COALESCE((
          SELECT COUNT(*)
            FROM bids b
            CROSS JOIN LATERAL jsonb_array_elements(COALESCE(b.milestones, '[]'::jsonb)) ms
           WHERE b.proposal_id = p.proposal_id
             AND NULLIF(ms->>'paymentTxHash','') IS NOT NULL
        ), 0) AS agg_ms_paid,

        -- Last activity: newest among proposal updated/created, any bid created, any proof updated/submitted, any paymentDate in milestones
        GREATEST(
          p.updated_at,
          p.created_at,
          COALESCE((
            SELECT MAX(b.created_at)
              FROM bids b
             WHERE b.proposal_id = p.proposal_id
          ), TIMESTAMP 'epoch'),
          COALESCE((
            SELECT MAX(GREATEST(COALESCE(pr.updated_at, TIMESTAMP 'epoch'), COALESCE(pr.submitted_at, TIMESTAMP 'epoch')))
              FROM proofs pr
             WHERE pr.bid_id IN (SELECT bid_id FROM bids b WHERE b.proposal_id = p.proposal_id)
          ), TIMESTAMP 'epoch'),
          COALESCE((
            SELECT MAX(NULLIF(ms->>'paymentDate','')::timestamptz)
              FROM bids b
              CROSS JOIN LATERAL jsonb_array_elements(COALESCE(b.milestones, '[]'::jsonb)) ms
             WHERE b.proposal_id = p.proposal_id
          ), TIMESTAMP 'epoch')
        ) AS last_activity_at
      FROM proposals p
      ${whereSql}
      ORDER BY ${sortSql}
      LIMIT ${pageSize} OFFSET ${offset}
    `;

    const { rows } = await pool.query(sql, params);

    // Keep snake_case aggregates to avoid touching your UI; key names are explicit
    res.json({
      page, pageSize, total: cnt,
      items: rows.map(r => ({
        id: r.id,
        title: r.title,
        status: r.status,
        owner_wallet: r.owner_wallet,
        owner_email: r.owner_email,
        created_at: r.created_at,
        updated_at: r.updated_at,
        bids_total: Number(r.agg_bids_total || 0),
        bids_approved: Number(r.agg_bids_approved || 0),
        milestones_total: Number(r.agg_ms_total || 0),
        milestones_completed: Number(r.agg_ms_completed || 0),
        milestones_paid: Number(r.agg_ms_paid || 0),
        last_activity_at: r.last_activity_at
      }))
    });
  } catch (err) {
    console.error("GET /projects error", err);
    res.status(500).json({ error: "Server error" });
  }
});

// ==============================
// Project Overview (single project “everything”)
// ==============================
app.get("/projects/:id/overview", requireApprovedVendorOrAdmin, async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid project id" });

  try {
    // Load proposal (your PK is proposal_id)  // :contentReference[oaicite:4]{index=4}
    const { rows: prjRows } = await pool.query(
      `SELECT proposal_id, title, status, owner_wallet, owner_email, created_at, updated_at
         FROM proposals
        WHERE proposal_id = $1`,
      [id]
    );
    const prj = prjRows[0];
    if (!prj) return res.status(404).json({ error: "Not found" });

    // Auth: admin OR proposal owner (reuse your JWT semantics)  // :contentReference[oaicite:5]{index=5}
    const isAdmin = String(req.user?.role || '').toLowerCase() === 'admin';
    const myWallet = String(req.user?.sub || '').toLowerCase();
    if (!isAdmin && String(prj.owner_wallet || '').toLowerCase() !== myWallet) {
      return res.status(403).json({ error: "Forbidden" });
    }

    // Bids for this proposal (include doc + files)
    const { rows: bidRows } = await pool.query(
      `SELECT bid_id,
          proposal_id,
          vendor_name,
          wallet_address,
          price_usd,
          days,
          notes,
          preferred_stablecoin,
          milestones,
          status,
          created_at,
          updated_at,
          doc,
          COALESCE(files, '[]'::jsonb) AS files
     FROM bids
    WHERE proposal_id = $1
    ORDER BY created_at ASC`,
      [id]
    );

    // 2. INSERT THIS FIX: Hydrate bids with payment status (clears "Pending" if tx exists)
    const hydratedBids = await Promise.all(
      bidRows.map(b => overlayPaidFromMp(b, pool))
    );

    // 3. Update the next line to use 'hydratedBids' instead of 'bidRows'
    const bidsOut = hydratedBids.map(r => {
      let doc = r.doc;
      if (typeof doc === 'string') { try { doc = JSON.parse(doc); } catch { } }

      let files = r.files;
      if (typeof files === 'string') { try { files = JSON.parse(files); } catch { } }
      if (!Array.isArray(files)) files = files ? [files] : [];

      return { ...r, doc: doc || null, files };
    });

    const bidIds = bidsOut.map(b => b.bid_id);

    // Load proofs for all bids of this project
    let proofs = [];
    if (bidIds.length) {
      const { rows: proofRows } = await pool.query(
        `SELECT proof_id, bid_id, milestone_index, title, description, status,
            files, file_meta, gps_lat, gps_lon, capture_time, submitted_at, updated_at
       FROM proofs
      WHERE bid_id = ANY($1::bigint[])
      ORDER BY submitted_at ASC`,
        [bidIds]
      );

      // Sanitize + add safe geo (keeps submitted_at for your activity timeline)
      proofs = await Promise.all(proofRows.map(async pr => ({
        proof_id: pr.proof_id,
        bid_id: pr.bid_id,
        milestone_index: pr.milestone_index,
        title: pr.title,
        description: pr.description,
        status: pr.status,
        files: Array.isArray(pr.files)
          ? pr.files
          : (typeof pr.files === 'string' ? JSON.parse(pr.files || '[]') : []),
        submitted_at: pr.submitted_at,
        updated_at: pr.updated_at,
        taken_at: pr.capture_time || null,          // EXIF-derived time you store
        location: await buildSafeGeoForProof(pr)    // city/state/country + rounded coords
      })));
    }

    // Build milestone list: combine bid.milestones JSON + proof status + payments (paymentTxHash)
    const approvedProof = new Set(
      proofs.filter(p => String(p.status).toLowerCase() === 'approved')
        .map(p => `${p.bid_id}:${p.milestone_index}`)
    );

    const msItems = [];
    const paymentsActivity = [];
    for (const b of bidsOut) {
      const arr = Array.isArray(b.milestones) ? b.milestones
        : typeof b.milestones === 'string' ? JSON.parse(b.milestones || '[]')
          : [];
      arr.forEach((m, idx) => {
        const key = `${b.bid_id}:${idx}`;
        const paid = !!(m && m.paymentTxHash);
        const completed = paid || approvedProof.has(key) || !!m?.completed;
        if (paid && m.paymentDate) {
          paymentsActivity.push({
            type: 'milestone_paid',
            at: m.paymentDate,
            bid_id: b.bid_id,
            milestone_index: idx,
            amount_usd: m.amount ?? null,
            tx_hash: m.paymentTxHash
          });
        }
        msItems.push({
          bid_id: b.bid_id,
          index: idx,
          title: m?.name || `Milestone ${idx + 1}`,
          amount_usd: m?.amount ?? null,
          status: paid ? 'paid' : (completed ? 'completed' : 'pending'),
          submitted_proof_id: null, // linked below if we want
          completed_at: m?.completionDate || null,
          paid_at: paid ? (m?.paymentDate || null) : null,
          tx_hash: paid ? (m?.paymentTxHash || null) : null
        });
      });
    }

    const milestones = {
      total: msItems.length,
      completed: msItems.filter(x => x.status === 'completed' || x.status === 'paid').length,
      paid: msItems.filter(x => x.status === 'paid').length,
      items: msItems
    };

    // Activity (synthesized: created, bids, proofs, payments)
    const activity = [
      { type: 'proposal_created', at: prj.created_at, actor_role: 'owner' },
      // You don't persist approved_at; status flip happens but no timestamp. We skip it here.  // :contentReference[oaicite:7]{index=7}
      ...bidsOut.map(b => ({ type: 'bid_submitted', at: b.created_at, bid_id: b.bid_id, actor_role: 'vendor', vendor_name: b.vendor_name })),
      ...proofs.map(p => ({ type: 'proof_submitted', at: p.submitted_at, proof_id: p.proof_id, bid_id: p.bid_id, milestone_index: p.milestone_index })),
      ...paymentsActivity
    ].filter(Boolean).sort((a, b) => new Date(a.at).getTime() - new Date(b.at).getTime());

    return res.json({
      proposal: {
        id: prj.proposal_id,
        title: prj.title,
        status: prj.status,
        owner_wallet: prj.owner_wallet,
        owner_email: prj.owner_email,
        created_at: prj.created_at,
        updated_at: prj.updated_at
      },
      bids: {
        total: bidsOut.length,
        approved: bidsOut.filter(b => String(b.status).toLowerCase() === 'approved').length,
        items: bidsOut
      },
      milestones,
      proofs,
      activity
    });
  } catch (err) {
    console.error("GET /projects/:id/overview error", err);
    res.status(500).json({ error: "Server error" });
  }
});

// ==================================================================
// ROBUST TOKEN ROUTE: Implements "Cache" + "Emergency Fallback"
// This guarantees the frontend ALWAYS gets a token, even if Pinata is down/blocking.
// ==================================================================
// ==================================================================
// ROBUST TOKEN ROUTE: Implements "Cache" + "Emergency Fallback"
// This guarantees the frontend ALWAYS gets a token, even if Pinata is down/blocking.
// ==================================================================
const _cachedPinataTokens = {}; // tenantId -> { data, expiresAt }

app.get("/auth/pinata-token", requireAuth, async (req, res) => {
  try {
    const tenantId = req.tenantId || 'global';

    // 1. SERVE CACHE: If we have a valid key in memory, use it.
    const cached = _cachedPinataTokens[tenantId];
    if (cached && cached.expiresAt > Date.now()) {
      return res.json(cached.data);
    }

    console.log(`Attempting to generate new Pinata Token for tenant ${tenantId}...`);

    // Fetch tenant config
    const tenantJwt = await tenantService.getTenantConfig(req.tenantId, 'pinata_jwt');
    const jwtToUse = tenantJwt;

    if (!jwtToUse) {
      return res.status(500).json({ error: "Pinata not configured" });
    }

    const uuid = crypto.randomUUID();
    const body = {
      keyName: `upload_key_${uuid}`,
      permissions: { admin: true }, // Force admin to avoid syntax errors
      maxUses: 10000
    };

    const response = await fetch("https://api.pinata.cloud/users/generateApiKey", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "Authorization": `Bearer ${jwtToUse}`
      },
      body: JSON.stringify(body)
    });

    // 2. SUCCESS: If Pinata gives us a key, cache it and return it.
    if (response.ok) {
      const keyData = await response.json();

      _cachedPinataTokens[tenantId] = {
        data: keyData,
        expiresAt: Date.now() + (24 * 60 * 60 * 1000) // 24 hours
      };

      return res.json(keyData);
    }

    // 3. EMERGENCY FALLBACK: If Pinata says "Rate Limited" (429) or fails
    // We manually construct a token object using your SERVER'S existing JWT.
    // This bypasses the "Generate" endpoint completely.
    console.warn("⚠️ Pinata KeyGen Failed (Rate Limit). Using Emergency Fallback.");

    const fallbackData = {
      JWT: jwtToUse,               // Use the configured key so upload succeeds
      pinata_api_key: "",          // Not needed for JWT auth
      pinata_api_secret: ""        // Not needed for JWT auth
    };

    // Cache this fallback too, so we don't keep hitting the API error
    _cachedPinataTokens[tenantId] = {
      data: fallbackData,
      expiresAt: Date.now() + (1 * 60 * 60 * 1000) // Cache fallback for 1 hour
    };

    return res.json(fallbackData);

  } catch (err) {
    console.error("Pinata Token Route Fatal Error:", err);
    // Even on fatal crash, try to send the main JWT
    // Fetch config again just in case (or use global fallback)
    const tenantJwt = await tenantService.getTenantConfig(req.tenantId, 'pinata_jwt').catch(() => null);
    res.json({ JWT: tenantJwt });
  }
});

// ==============================
// Routes — Payments (legacy)
// ==============================
app.post("/payments/release", adminGuard, async (req, res) => {
  try {
    const { bidId, milestoneIndex } = req.body;
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1 AND tenant_id=$2", [bidId, req.tenantId]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });

    const bid = rows[0];
    const milestones = Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || "[]");
    if (!milestones[milestoneIndex]) return res.status(400).json({ error: "Invalid milestone" });

    const ms = milestones[milestoneIndex];
    if (!ms.completed) return res.status(400).json({ error: "Milestone not completed" });

    const receipt = await blockchainService.sendToken(
      bid.preferred_stablecoin,
      bid.wallet_address,
      ms.amount,
      req.tenantId
    );
    res.json({ success: true, receipt });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// Normalize client-provided milestones into the DB shape
function normalizeMilestone(x) {
  return {
    name: String(x?.name || 'Milestone'),
    amount: Number(x?.amount) || 0,
    dueDate: new Date(x?.dueDate || Date.now()).toISOString(),
    acceptance: Array.isArray(x?.acceptance) ? x.acceptance : [],
    archived: !!x?.archived,
  };
}

// ==============================
// Routes — IPFS via Pinata
// ==============================
// -------------------------------------------------------
// 1. GLOBAL QUEUE: Prevents parallel requests from crashing the server
// -------------------------------------------------------
let globalPinataQueue = Promise.resolve();

app.post("/ipfs/upload-file", async (req, res) => {
  try {
    if (!req.files || !req.files.file) return res.status(400).json({ error: "No file uploaded" });

    const fileInput = req.files.file;
    const files = Array.isArray(fileInput) ? fileInput : [fileInput];
    const results = [];

    // 2. QUEUEING LOGIC: Wait for previous uploads to finish before starting this batch
    // This effectively locks the upload process to one-at-a-time across the whole server.
    await (globalPinataQueue = globalPinataQueue.then(async () => {
      for (const f of files) {
        try {
          // Upload
          const result = await pinataUploadFile(f, req.tenantId);
          results.push(result);

          // 3. SAFETY DELAY: 1000ms is safer than 300ms for free/tier-1 plans
          console.log(`[Pinata] Uploaded ${f.name}. Waiting...`);
          await new Promise(r => setTimeout(r, 1500));
        } catch (innerErr) {
          console.error(`[Pinata] Failed to upload ${f.name}`, innerErr);
          throw innerErr; // Stop this batch if a file fails
        }
      }
    }).catch(err => {
      // If the queue broke, re-throw so we send a 500 error below
      throw err;
    }));

    res.json(files.length === 1 ? results[0] : results);
  } catch (err) {
    console.error("Upload error:", err);
    res.status(500).json({ error: err.message });
  }
});

// ✅ QUEUE-PROTECTED JSON ROUTE
// This prevents the "Proposal JSON" step from crashing due to rate limits
app.post("/ipfs/upload-json", async (req, res) => {
  try {
    // Add to the SAME global queue as the files
    await (globalPinataQueue = globalPinataQueue.then(async () => {

      // 1. Attempt the upload
      const result = await pinataUploadJson(req.body || {}, req.tenantId);

      // 2. Safety delay: Cool down the API key after this upload
      console.log(`[Pinata] Uploaded JSON Metadata. Waiting...`);
      await new Promise(r => setTimeout(r, 2000));

      // 3. Send response
      res.json(result);

    }).catch(err => {
      // If the queue fails, throw so the outer catch block handles it
      throw err;
    }));

  } catch (err) {
    console.error("JSON Upload error:", err);
    res.status(500).json({ error: err.message });
  }
});

// POST /templates  (admin upsert)
// Body: { slug, title, locale?, category?, summary?, default_currency?, milestones:[{idx,name,amount,days_offset,acceptance[]}] }
app.post('/templates', adminGuard, async (req, res) => {
  const c = req.body || {};
  if (!c.slug || !c.title) return res.status(400).json({ error: 'slug_and_title_required' });

  try {
    await pool.query('BEGIN');

    const { rows: t } = await pool.query(
      `INSERT INTO templates (slug, title, locale, category, summary, default_currency, updated_at)
       VALUES ($1,$2,$3,$4,$5,$6, now())
       ON CONFLICT (slug) DO UPDATE SET
         title=EXCLUDED.title, locale=EXCLUDED.locale, category=EXCLUDED.category,
         summary=EXCLUDED.summary, default_currency=EXCLUDED.default_currency, updated_at=now()
       RETURNING template_id`,
      [c.slug, c.title, c.locale || 'en', c.category || null, c.summary || null, c.default_currency || 'USD']
    );

    const tid = t[0].template_id;
    await pool.query(`DELETE FROM template_milestones WHERE template_id=$1`, [tid]);

    const ms = Array.isArray(c.milestones) ? c.milestones : [];
    for (const m of ms) {
      await pool.query(
        `INSERT INTO template_milestones (template_id, idx, name, amount, days_offset, acceptance)
         VALUES ($1,$2,$3,$4,$5,$6)`,
        [tid, m.idx, m.name, Number(m.amount) || 0, Number(m.days_offset) || 0, JSON.stringify(m.acceptance || [])]
      );
    }

    await pool.query('COMMIT');
    res.json({ ok: true, templateId: tid });
  } catch (e) {
    await pool.query('ROLLBACK');
    res.status(500).json({ error: 'create_or_update_template_failed' });
  }
});

// POST /bids/from-template  (vendor/admin)
// Body: { slug? | templateId?, proposalId, vendorName, walletAddress, preferredStablecoin?, files?: string[], milestones?: [...] }
// Notes: If milestones are provided, they override the template; otherwise build from template days_offset.
app.post('/bids/from-template', requireApprovedVendorOrAdmin, async (req, res) => {
  try {
    const b = req.body || {};
    const selector = b.templateId ?? b.slug;
    if (!selector) return res.status(400).json({ error: 'template_required' });
    if (!b.proposalId) return res.status(400).json({ error: 'proposalId_required' });
    if (!b.vendorName) return res.status(400).json({ error: 'vendorName_required' });
    if (!/^0x[a-fA-F0-9]{40}$/.test(String(b.walletAddress || '')))
      return res.status(400).json({ error: 'wallet_invalid' });

    const isId = /^\d+$/.test(String(selector));
    const { rows: t } = await pool.query(
      `SELECT template_id, title FROM templates WHERE ${isId ? 'template_id' : 'slug'}=$1 LIMIT 1`,
      [isId ? Number(selector) : String(selector)]
    );
    if (!t[0]) return res.status(404).json({ error: 'template_not_found' });

    const tid = t[0].template_id;
    const { rows: msRows } = await pool.query(
      `SELECT idx, name, amount, days_offset, acceptance
         FROM template_milestones
        WHERE template_id=$1
        ORDER BY idx ASC`,
      [tid]
    );

    const now = Date.now();

    // Prefer client-provided milestones; fallback to template-based
    const ms = Array.isArray(b.milestones) && b.milestones.length
      ? b.milestones.map(x => normalizeMilestone(x))
      : msRows.map(r => ({
        name: r.name,
        amount: Number(r.amount) || 0,
        dueDate: new Date(now + (Number(r.days_offset) || 0) * 86400 * 1000).toISOString(),
        acceptance: r.acceptance || [],
        archived: false,
      }));

    // Totals/duration
    const priceUSD = ms.reduce((a, m) => a + (Number(m.amount) || 0), 0);
    const days = Math.max(
      0,
      ...ms.map(m => {
        const ts = Date.parse(m.dueDate);
        return Number.isFinite(ts) ? Math.ceil((ts - now) / (86400 * 1000)) : 0;
      })
    );

    const notes = b.notes || `Created from template "${t[0].title}"`;
    const preferred = String(b.preferredStablecoin || 'USDT').toUpperCase() === 'USDC' ? 'USDC' : 'USDT';
    const files = Array.isArray(b.files)
      ? b.files
        .map(x =>
          typeof x === 'string'
            ? { url: x }
            : {
              url: String(x?.url || ''),
              name: x?.name || (String(x?.url || '').split('/').pop() || 'file'),
              cid: x?.cid ?? null,
              mimetype: x?.mimetype || x?.contentType || null,
            }
        )
        .filter(f => f.url)
      : [];

    const doc = files.length > 0 ? files[0] : null;

    // --- insert same shape as /bids route ---
    const insertQ = `
      INSERT INTO bids (
        proposal_id,
        vendor_name,
        price_usd,
        days,
        notes,
        wallet_address,
        preferred_stablecoin,
        milestones,
        doc,
        files,
        status,
        created_at,
        tenant_id
      )
      VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,'pending', NOW(), $11)
      RETURNING *`;

    const insertVals = [
      Number(b.proposalId),
      String(b.vendorName),
      priceUSD,
      days,
      notes,
      String(b.walletAddress),
      preferred,
      JSON.stringify(ms),
      JSON.stringify(doc),
      JSON.stringify(files),
      req.tenantId
    ];

    const { rows } = await pool.query(insertQ, insertVals);
    const inserted = rows[0];

    try {
      const actorWallet = (req.user && (req.user.address || req.user.sub)) || null;
      const actorRole = (req.user && req.user.role) || "vendor";

      const ins = await pool.query(
        `INSERT INTO bid_audits (bid_id, actor_wallet, actor_role, changes)
     VALUES ($1,$2,$3,$4)
     RETURNING audit_id`,
        [Number(inserted.bid_id), actorWallet, actorRole, { created: true, source: 'template' }]
      );
      if (typeof enrichAuditRow === "function") {
        enrichAuditRow(pool, ins.rows[0].audit_id, pinataUploadFile).catch(() => null);
      }
    } catch (e) {
      console.error("Template bid audit failed:", e);
    }

    // Inline Agent2 analysis (same behavior as /bids)
    const { rows: pr } = await pool.query(`SELECT * FROM proposals WHERE proposal_id=$1`, [inserted.proposal_id]);
    const prop = pr[0] || null;

    const INLINE_ANALYSIS_DEADLINE_MS = Number(process.env.AGENT2_INLINE_TIMEOUT_MS || 12000);
    const analysis = await withTimeout(
      prop
        ? runAgent2OnBid(inserted, prop, { tenantId: req.tenantId })
        : Promise.resolve({
          status: 'error',
          summary: 'Proposal not found for analysis.',
          risks: [],
          fit: 'low',
          milestoneNotes: [],
          confidence: 0,
          pdfUsed: false,
        }),
      INLINE_ANALYSIS_DEADLINE_MS,
      {
        status: 'timeout',
        summary: 'Analysis timed out.',
        risks: [],
        fit: 'low',
        milestoneNotes: [],
        confidence: 0,
        pdfUsed: false,
      }
    );

    await pool.query(`UPDATE bids SET ai_analysis=$1 WHERE bid_id=$2`, [
      JSON.stringify(analysis),
      inserted.bid_id,
    ]);

    res.json({ ok: true, bidId: inserted.bid_id });
  } catch (e) {
    res.status(500).json({ error: 'failed_create_bid_from_template' });
  }
});

/// ==============================
// Sally Uyuni App Routes
// ==============================

// --- 0. DB MIGRATION: Ensure reports have status columns ---
(async () => {
  try {
    await pool.query(`
      ALTER TABLE school_reports
      ADD COLUMN IF NOT EXISTS status TEXT DEFAULT 'pending',
      ADD COLUMN IF NOT EXISTS tx_hash TEXT;
    `);
    console.log('[db] Verified status columns on school_reports');
  } catch (e) {
    console.error('[db] Failed to migrate school_reports:', e);
  }
})();

// --- 1. HELPER: Calculate Distance (Haversine Formula) ---
function getDistanceFromLatLonInKm(lat1, lon1, lat2, lon2) {
  const R = 6371; // Radius of the earth in km
  const dLat = deg2rad(lat2 - lat1);
  const dLon = deg2rad(lon2 - lon1);
  const a =
    Math.sin(dLat / 2) * Math.sin(dLat / 2) +
    Math.cos(deg2rad(lat1)) * Math.cos(deg2rad(lat2)) * Math.sin(dLon / 2) * Math.sin(dLon / 2);
  const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
  const d = R * c; // Distance in km
  return d;
}

function deg2rad(deg) {
  return deg * (Math.PI / 180);
}

// --- 2. GET ROUTE: Fetch Reports (Missing Piece!) ---
app.get('/api/reports', async (req, res) => {
  try {
    // 1. Check Auth (Admin or explicit role)
    // Relaxed for this demo, but ideally verify req.user

    // 2. Parse Filters
    const statusParam = String(req.query.status || 'all').toLowerCase();

    let query = "SELECT * FROM school_reports";
    const params = [req.tenantId];
    const conditions = ["tenant_id = $1"];

    // Filter Logic
    if (statusParam !== 'all') {
      if (statusParam === 'completed' || statusParam === 'paid') {
        // Frontend 'completed' maps to DB 'paid'
        conditions.push("(status = 'paid' OR status = 'completed')");
      } else {
        params.push(statusParam);
        conditions.push(`status = $${params.length}`);
      }
    }

    if (conditions.length > 0) {
      query += " WHERE " + conditions.join(" AND ");
    }

    query += " ORDER BY created_at DESC";

    const { rows } = await pool.query(query, params);
    res.json(rows);

  } catch (err) {
    console.error("GET /api/reports error:", err);
    res.status(500).json({ error: "Failed to fetch reports" });
  }
});

// --- 3. ROUTE: Submit Report & Pay Reward (SPLIT LOGIC) ---
app.post('/api/reports', authRequired, async (req, res) => {
  try {
    const {
      id,
      category, // 'food' or 'infrastructure'
      schoolName,
      description,
      rating,
      imageCid,
      imageUrl,
      aiAnalysis = {},
      location // Device location
    } = req.body;

    const wallet = String(req.user?.sub || "").toLowerCase();

    // ============================================================
    // STEP 1: PREPARE LOCATIONS (Normalize Data)
    // ============================================================

    // Helper: Normalize Coords
    const normalizeCoords = (loc) => {
      if (!loc) return null;
      let obj = loc;
      if (typeof loc === 'string') { try { obj = JSON.parse(loc); } catch { return null; } }
      if (typeof obj !== 'object') return null;

      const lat = obj.lat ?? obj.latitude ?? (Array.isArray(obj.coordinates) ? obj.coordinates[1] : null);
      const lon = obj.lng ?? obj.lon ?? obj.longitude ?? (Array.isArray(obj.coordinates) ? obj.coordinates[0] : null);

      if (lat != null && lon != null && !isNaN(Number(lat)) && Number(lat) !== 0) {
        return { lat: Number(lat), lon: Number(lon) };
      }
      return null;
    };

    // A. Get Device Location
    let reportLoc = normalizeCoords(location);
    let imageLoc = null;

    // B. Extract Image EXIF (Security Check)
    if (imageUrl) {
      try {
        const meta = await extractFileMetaFromUrl({ url: imageUrl });
        if (meta?.exif?.gpsLatitude) {
          imageLoc = { lat: meta.exif.gpsLatitude, lon: meta.exif.gpsLongitude };

          // Add to analysis
          aiAnalysis.geo = {
            lat: meta.exif.gpsLatitude,
            lon: meta.exif.gpsLongitude,
            source: "image_exif"
          };

          // Trust Image GPS over Device GPS if available
          reportLoc = imageLoc;
        }
      } catch (exifErr) { console.warn("EXIF skipped:", exifErr.message); }
    }

    let finalAnalysis = { ...aiAnalysis };
    let proposalMatch = null;

    // ============================================================
    // STEP 2: CATEGORY-SPECIFIC VERIFICATION
    // ============================================================

    if (category === 'infrastructure') {
      // --- LOGIC A: INFRASTRUCTURE (No Proposal Check) ---
      finalAnalysis.vendor = "N/A (Infrastructure)";

      // Validation: Must have valid GPS data
      if (reportLoc) {
        finalAnalysis.verification = "verified_gps_only";
        finalAnalysis.location_status = "gps_present";
        finalAnalysis.highlights = [...(finalAnalysis.highlights || []), "Location Data Present"];
      } else {
        finalAnalysis.verification = "missing_gps";
        finalAnalysis.location_status = "no_gps_data";
      }

    } else {
      // --- LOGIC B: FOOD (Strict Proposal Match) ---

      // 1. Fetch Active Food Proposals (Include tenant_id)
      const { rows: candidates } = await pool.query(`
          SELECT p.proposal_id, p.org_name, p.title, p.location, p.tenant_id, b.vendor_name
          FROM proposals p
          JOIN bids b ON b.proposal_id = p.proposal_id
          WHERE LOWER(b.status) IN ('approved', 'completed', 'paid', 'funded')
        `);

      // 2. Fuzzy Match School Name
      const normalizeStr = (str) => (str || "").normalize("NFD").replace(/[\u0300-\u036f]/g, "").toLowerCase().trim();
      const targetName = normalizeStr(schoolName);

      proposalMatch = candidates.find(c => {
        const rawDb = normalizeStr(c.org_name + " " + c.title);
        return rawDb.includes(targetName) || targetName.includes(rawDb);
      });

      // 3. Verify Distance
      const proposalLoc = proposalMatch ? normalizeCoords(proposalMatch.location) : null;

      if (proposalMatch) {
        finalAnalysis.vendor = proposalMatch.vendor_name;
        finalAnalysis.proposal_id = proposalMatch.proposal_id;
        // Capture tenant ID from the matched proposal
        req.tenantId = proposalMatch.tenant_id;

        if (proposalLoc && reportLoc) {
          const dist = getDistanceFromLatLonInKm(reportLoc.lat, reportLoc.lon, proposalLoc.lat, proposalLoc.lon);
          finalAnalysis.distance_km = dist.toFixed(3);

          if (dist <= 0.5) {
            finalAnalysis.verification = "verified_match"; // Success
            finalAnalysis.location_status = "match";
          } else {
            finalAnalysis.verification = "flagged_distance"; // Fail
            finalAnalysis.location_status = "mismatch";
          }
        } else {
          finalAnalysis.verification = "unknown_gps";
        }
      } else {
        finalAnalysis.vendor = "Unknown Vendor";
        finalAnalysis.verification = "proposal_not_found";
      }
    }

    // ============================================================
    // STEP 3: SAVE REPORT
    // ============================================================
    // Fallback to default tenant if not matched (e.g. infrastructure or failed match)
    const targetTenantId = req.tenantId || '00000000-0000-0000-0000-000000000000';

    await pool.query(
      `INSERT INTO school_reports 
       (report_id, school_name, description, rating, image_cid, image_url, ai_analysis, location, wallet_address, status, created_at, tenant_id)
       VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, 'pending', NOW(), $10)
       ON CONFLICT (report_id) DO NOTHING`,
      [
        id, schoolName, description, rating, imageCid || null, imageUrl || null,
        JSON.stringify(finalAnalysis), JSON.stringify(location || {}), wallet, targetTenantId
      ]
    );

    // ============================================================
    // STEP 4: PAYMENT GATING
    // ============================================================

    let isPayable = false;
    let rejectReason = "";

    // CHECK 1: CATEGORY SPECIFIC CONTENT
    let contentValid = false;
    if (category === 'infrastructure') {
      // Needs Severity > 0
      if (finalAnalysis.severity > 0) contentValid = true;
      else rejectReason = "no_damage_detected";
    } else {
      // Needs Food Score > 0
      if (finalAnalysis.score > 0 || finalAnalysis.isFood === true) contentValid = true;
      else rejectReason = "no_food_detected";
    }

    // CHECK 2: LOCATION VERIFICATION
    let locationValid = false;
    if (category === 'infrastructure') {
      // Infra: Just needs valid GPS data (Since no proposal to match)
      if (finalAnalysis.verification === 'verified_gps_only') locationValid = true;
      else rejectReason = "missing_gps_data";
    } else {
      // Food: Must match DB Proposal
      if (finalAnalysis.verification === 'verified_match') locationValid = true;
      else rejectReason = `location_verification_failed (${finalAnalysis.verification})`;
    }

    // FINAL DECISION
    if (contentValid && locationValid) {
      isPayable = true;
    }

    let txHash = null;
    let finalStatus = rejectReason || 'pending';

    if (isPayable) {
      try {
        console.log(`[Reward] Sending 0.05 USDT to ${wallet} for ${category} report.`);
        const receipt = await blockchainService.sendToken("USDT", wallet, 0.05, req.tenantId);
        txHash = receipt.hash;
        finalStatus = 'paid';
      } catch (payErr) {
        console.error(`[Reward] Payment failed:`, payErr.message);
        finalStatus = 'payment_failed';
      }
    } else {
      console.log(`[Reward] Skipped. Category: ${category}, Reason: ${rejectReason}`);
    }

    // Update Status
    await pool.query(
      `UPDATE school_reports SET status = $1, tx_hash = $2 WHERE report_id = $3 AND tenant_id = $4`,
      [finalStatus, txHash, id, req.tenantId]
    );

    res.json({
      success: true,
      rewardTx: txHash,
      status: finalStatus,
      identifiedVendor: finalAnalysis.vendor,
      verification: finalAnalysis.verification
    });

  } catch (err) {
    console.error("POST /api/reports error:", err);
    res.status(500).json({ error: "Failed to submit report" });
  }
});

// --- 4. DELETE ROUTE: Permanently remove a report ---
app.delete('/api/reports/:id', authRequired, async (req, res) => {
  try {
    const { id } = req.params;
    const wallet = String(req.user?.sub || "").toLowerCase();

    // Check if Admin
    const isAdmin = (req.user?.role === 'admin') || isAdminAddress(wallet);

    let query;
    let params;

    if (isAdmin) {
      // Admin can delete ANY report
      query = 'DELETE FROM school_reports WHERE report_id = $1 AND tenant_id = $2';
      params = [id, req.tenantId];
    } else {
      // Users can only delete THEIR OWN reports
      query = 'DELETE FROM school_reports WHERE report_id = $1 AND lower(wallet_address) = lower($2) AND tenant_id = $3';
      params = [id, wallet, req.tenantId];
    }

    const { rowCount } = await pool.query(query, params);

    if (rowCount === 0) {
      return res.status(404).json({ error: "Report not found or unauthorized" });
    }

    res.json({ success: true, deletedId: id });

  } catch (err) {
    console.error("DELETE /api/reports error:", err);
    res.status(500).json({ error: "Failed to delete report" });
  }
});

// --- 5. ARCHIVE ROUTE: Mark as archived (Soft Delete) ---
app.put('/api/reports/:id/archive', authRequired, async (req, res) => {
  try {
    const { id } = req.params;
    const wallet = String(req.user?.sub || "").toLowerCase();
    const isAdmin = (req.user?.role === 'admin') || isAdminAddress(wallet);

    let query;
    let params;

    if (isAdmin) {
      query = "UPDATE school_reports SET status = 'archived' WHERE report_id = $1 AND tenant_id = $2";
      params = [id, req.tenantId];
    } else {
      query = "UPDATE school_reports SET status = 'archived' WHERE report_id = $1 AND lower(wallet_address) = lower($2) AND tenant_id = $3";
      params = [id, wallet, req.tenantId];
    }

    const { rowCount } = await pool.query(query, params);

    if (rowCount === 0) {
      return res.status(404).json({ error: "Report not found or unauthorized" });
    }

    res.json({ success: true, id, status: 'archived' });

  } catch (err) {
    console.error("ARCHIVE /api/reports error:", err);
    res.status(500).json({ error: "Failed to archive report" });
  }
});

// ==============================
// Start server
// ==============================
app.listen(PORT, () => {
  console.log(`[api] Listening on :${PORT}`);
  console.log(`[api] Admin enforcement: ${ENFORCE_JWT_ADMIN ? "ON" : "OFF"}`);
  console.log(`[api] Vendor scoping:    ${SCOPE_BIDS_FOR_VENDOR ? "ON" : "OFF"}`);
});

// ==============================
// Start blockchain event sync (viem)
// ==============================
(async () => {
  try {
    if (process.env.ENABLE_EVENT_SYNC !== 'false') {
      const { startEventSync } = await import('./services/eventSync.mjs');
      await startEventSync();
      console.log('[eventSync] started');
    } else {
      console.log('[eventSync] disabled via ENABLE_EVENT_SYNC=false');
    }
  } catch (err) {
    console.error('[eventSync] failed to start:', err?.message || err);
  }
})();