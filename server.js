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
// ==== SAFE CONFIG (define once, near the top) ====
const SAFE_ADDRESS       = (process.env.SAFE_ADDRESS || process.env.SAFE_WALLET || '0xedd1F37FD3eaACb596CDF00102187DA0cc884D93').trim();
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

// ==============================
// Config
// ==============================
const PORT = Number(process.env.PORT || 3000);
const DEFAULT_ORIGIN = "https://lithiumx.netlify.app";

const CORS_ORIGINS = (process.env.CORS_ORIGINS || process.env.CORS_ORIGIN || DEFAULT_ORIGIN)
  .split(",")
  .map((s) => s.trim())
  .filter(Boolean);

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

// ==============================
// Database
// ==============================
const pool = new Pool({
  connectionString: process.env.DATABASE_URL,
  ssl: { rejectUnauthorized: false },
});

// ---- Safe Tx overlay helpers (response-time hydration) ----
const SAFE_CACHE_TTL_MS = 5_000;

// ADD THIS — define once
const SAFE_LOOKUPS_PER_REQUEST =
  process.env.SAFE_LOOKUPS_PER_REQUEST !== undefined
    ? Math.max(0, Math.floor(Number(process.env.SAFE_LOOKUPS_PER_REQUEST)))
    : 8;

// Cache: safeTxHash -> { at, isExecuted, txHash }
const _safeStatusCache = _safeStatusCache || new Map();
const SAFE_CACHE_TTL_MS = typeof SAFE_CACHE_TTL_MS === 'number' ? SAFE_CACHE_TTL_MS : 5_000;
const _safeTxUrlBase = (_safeTxUrlBase || (process.env.SAFE_TXSERVICE_URL || 'https://api.safe.global/tx-service/sep').trim().replace(/\/+$/, ''));

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
async function _finalizePaidInDb({ bidId, milestoneIndex, txHash, safeTxHash }) {
  try {
    // Update milestone JSON
    const { rows: b } = await pool.query('SELECT milestones FROM bids WHERE bid_id=$1', [bidId]);
    if (!b[0]) return;
    const arr = Array.isArray(b[0].milestones) ? b[0].milestones : JSON.parse(b[0].milestones || '[]');
    const ms = { ...(arr[milestoneIndex] || {}) };
    const iso = new Date().toISOString();

    if (safeTxHash && !ms.safePaymentTxHash) ms.safePaymentTxHash = safeTxHash;
    ms.paymentTxHash  = ms.paymentTxHash || txHash || null;
    ms.paymentDate    = ms.paymentDate   || iso;
    ms.paidAt         = ms.paidAt        || ms.paymentDate;
    ms.paymentPending = false;
    ms.status         = 'paid';

    arr[milestoneIndex] = ms;
    await pool.query('UPDATE bids SET milestones=$1 WHERE bid_id=$2', [JSON.stringify(arr), bidId]);

    // Update milestone_payments (also switch to the new safe_tx_hash if the hash changed)
    await pool.query(
      `UPDATE milestone_payments
         SET status='released',
             safe_tx_hash = COALESCE($4, safe_tx_hash),
             tx_hash=COALESCE($3, tx_hash),
             released_at=COALESCE(released_at, NOW())
       WHERE bid_id=$1 AND milestone_index=$2`,
      [bidId, milestoneIndex, txHash || null, safeTxHash || null]
    );
  } catch (e) {
    console.warn('[overlay finalize] DB finalize failed', e?.message || e);
  }
}

// --- Overlay "Paid" status from milestone_payments into bid.milestones for responses ---
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
      WHERE bid_id = $1
      ORDER BY milestone_index, created_at DESC, id DESC`,
    [bidId]
  );

  if (!mpRows.length) {
    return { ...bid, milestones: msArr };
  }

  const byIdx = new Map(mpRows.map(r => [Number(r.milestone_index), r]));

  // Pass 1: mark already-released as paid (no network calls)
  for (let i = 0; i < msArr.length; i++) {
    const r = byIdx.get(i);
    if (!r) continue;

    const s = String(r.status || '').toLowerCase();
    const alreadyReleased = s === 'released' || !!r.tx_hash || !!r.released_at;

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
        paymentPending: false,
        status: 'paid',
      };
    }
  }

  // Build list of still-pending-with-safe rows, newest first
  let lookupsLeft =
    process.env.SAFE_LOOKUPS_PER_REQUEST !== undefined
      ? Math.max(0, Math.floor(Number(process.env.SAFE_LOOKUPS_PER_REQUEST)))
      : SAFE_LOOKUPS_PER_REQUEST;

  const pending = mpRows
    .filter(r => {
      const s = String(r.status || '').toLowerCase();
      const alreadyReleased = s === 'released' || !!r.tx_hash || !!r.released_at;
      return !alreadyReleased && r.safe_tx_hash != null;
    })
    .sort((a, b) => new Date(b.created_at || 0) - new Date(a.created_at || 0));

  // Pass 2: spend lookup budget; handle replaced Safe tx at same nonce
  const tasks = [];
  for (const r of pending) {
    if (lookupsLeft <= 0) break;
    lookupsLeft--;

    const idx = Number(r.milestone_index);
    if (!Number.isFinite(idx)) continue;

    const safeHash = r.safe_tx_hash;
    const nonce = r.safe_nonce ?? null;

    tasks.push((async () => {
      // 2a) Check the recorded safe tx hash
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
        await _finalizePaidInDb({ bidId, milestoneIndex: idx, txHash: st.txHash, safeTxHash: safeHash });
        return;
      }

      // 2b) Fallback: if a different Safe tx at the SAME NONCE got executed (rebroadcast / replacement)
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
        await _finalizePaidInDb({ bidId, milestoneIndex: idx, txHash: alt.txHash, safeTxHash: alt.safeTxHash });
        return;
      }

      // 2c) Still pending — keep in-flight markers for the UI
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

  // Any remaining pending we didn’t check (budget spent) → leave as submitted
  for (const r of pending.slice(lookupsLeft < 0 ? 0 : SAFE_LOOKUPS_PER_REQUEST)) {
    const idx = Number(r.milestone_index);
    if (!Number.isFinite(idx)) continue;
    msArr[idx] = {
      ...(msArr[idx] || {}),
      safePaymentTxHash: msArr[idx]?.safePaymentTxHash || r.safe_tx_hash,
      safeTxHash: msArr[idx]?.safeTxHash || r.safe_tx_hash,
      safeNonce: msArr[idx]?.safeNonce ?? r.safe_nonce ?? null,
      safeStatus: msArr[idx]?.safeStatus || 'submitted',
      paymentPending: true,
    };
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
      WHERE bid_id = ANY($1::bigint[])`,
    [bidIds]
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

      if (hit.status === 'pending') {
        // show the amber "Payment Pending" pill and hide the green button
        return { ...m, paymentPending: true };
      }
      if (hit.status === 'released') {
        // make sure the UI sees it as paid
        const tx = hit.tx_hash || m.paymentTxHash || null;
        return { ...m, paymentTxHash: tx, paid: true };
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
        ADD COLUMN IF NOT EXISTS updated_at    timestamptz NOT NULL DEFAULT now();
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

// Small helpers
function toE164(raw) {
  if (!raw) return null;
  const s = String(raw).replace(/[^\d+]/g, "");
  if (s.startsWith("+")) return s;
  return `${WA_DEFAULT_COUNTRY}${s}`;
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
  const toAddr   = ensureWaAddr(to);                   // e.g. whatsapp:+49XXXXXXXXX

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
  const toAddr   = ensureWaAddr(to);

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

// Notify admins when a *new* vendor signs in for the first time
async function notifyVendorSignup({ wallet, vendorName, email, phone }) {
  if (!NOTIFY_ENABLED) return;

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

  // bilingual wrapper (you already have bi())
  const en = lines.join('\n');
  const es = lines.join('\n');
  const { text, html } = bi(en, es);

  await Promise.allSettled([
    TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
    MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, 'Vendor signup — approval needed', html) : null,
    ...(ADMIN_WHATSAPP || []).map(n => sendWhatsApp(n, text)),
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
    const proposerEmails = [p.contact, p.owner_email].map(s => (s||"").trim()).filter(Boolean);
    const proposerPhone  = toE164(p.owner_phone || "");
    const proposerTg     = (p.owner_telegram_chat_id || "").trim();

    await Promise.all([
      // Admins
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, subject, html)      : null,
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
    const proposerEmails = [p.contact, p.owner_email].map(s => (s||"").trim()).filter(Boolean);
    const proposerPhone  = toE164(p.owner_phone || "");
    const proposerTg     = (p.owner_telegram_chat_id || "").trim();

    await Promise.all([
      // Admins
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, subject, html)      : null,
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
    const subject   = `✅ Bid awarded`;
    const title     = proposal?.title || "(untitled)";
    const org       = proposal?.org_name || "";
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
    const vendorEmails = [vendor?.email].map(s => (s||"").trim()).filter(Boolean);
    const vendorPhone  = toE164(vendor?.phone || "");
    const vendorTg     = (vendor?.telegram_chat_id || "").trim();

    await Promise.all([
      // Admins
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, subject, html)      : null,
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

    const vendorEmails = [vendor?.email].map(s => (s||"").trim()).filter(Boolean);
    const vendorPhone  = toE164(vendor?.phone || "");
    const vendorTg     = (vendor?.telegram_chat_id || "").trim();

    await Promise.all([
      // Admins
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, subject, html)      : null,
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
    `<div>${en.trim().replace(/\n/g,'<br>')}</div>`,
    '<hr>',
    `<div>${es.trim().replace(/\n/g,'<br>')}</div>`
  ].join('\n');
  return { text, html };
}

// ==============================
// Notifications — Payment pending approval
// ==============================
async function notifyPaymentPending({ bid, proposal, msIndex, amount, method = 'safe', txRef = null }) {
  try {
    const title     = proposal?.title || 'Project';
    const vendorStr = `${bid.vendor_name || ''} (${bid.wallet_address || ''})`.trim();
    const amountStr = `$${Number(amount || 0).toFixed(2)} USD`;
    const adminLink = APP_BASE_URL ? `${APP_BASE_URL}/admin/bids/${bid.bid_id}` : null;
    const subject   = method === 'safe'
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
      MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, subject, html)      : null,
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
    const vendorEmails = [vendor?.email].map(s => (s||"").trim()).filter(Boolean);
    const vendorPhone  = toE164(vendor?.phone || "");
    const vendorTg     = (vendor?.telegram_chat_id || "").trim();

    await Promise.all([
      // Admins
      TELEGRAM_ADMIN_CHAT_IDS?.length ? sendTelegram(TELEGRAM_ADMIN_CHAT_IDS, text) : null,
      MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, subject, html)      : null,
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
  const msIndex   = Number(proof.milestone_index) + 1;
  const subject   = `⚠️ Proof needs review — ${proposal?.title || "Project"} (Milestone ${msIndex})`;
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
      MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, subject, html)      : null,
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
    const subject   = `✅ Proof approved — ${proposal?.title || "Project"} (Milestone ${msIndex})`;
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
      MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, subject, html)      : null,
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
      [ (bid.wallet_address || "").toLowerCase() ]
    );
    const vp = vprows[0] || {};
    const vendorEmail = (vp.email || "").trim();
    const vendorPhone = toE164(vp.phone || "");
    const vendorTg    = (vp.telegram_chat_id || "").trim();

    await Promise.all([
      vendorTg    ? sendTelegram([vendorTg], text)          : null,
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
  const subject   = `💸 Payment released — ${proposal?.title || "Project"} (Milestone ${msIndex})`;
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
    MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, subject, html)      : null,
    ...(ADMIN_WHATSAPP || []).map(n =>
      TWILIO_WA_CONTENT_SID
        ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": proposal?.title || "", "2": "payment released" })
        : sendWhatsApp(n, text)
    ),
  ].filter(Boolean));

  // Vendor
  const { rows: vprows } = await pool.query(
    `SELECT email, phone, telegram_chat_id FROM vendor_profiles WHERE lower(wallet_address)=lower($1) LIMIT 1`,
    [ (bid.wallet_address || "").toLowerCase() ]
  );
  const vp = vprows[0] || {};
  const vendorEmail = (vp.email || "").trim();
  const vendorPhone = toE164(vp.phone || "");
  const vendorTg    = (vp.telegram_chat_id || "").trim();

  await Promise.all([
    vendorTg    ? sendTelegram([vendorTg], text)             : null,
    vendorEmail ? sendEmail([vendorEmail], subject, html)    : null,
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
    const title   = proposal?.title || 'Project';
    const bidStr  = `Bid ${bid?.bid_id ?? ''}`.trim();
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
      MAIL_ADMIN_TO?.length           ? sendEmail(MAIL_ADMIN_TO, subject, html)      : null,
      ...(ADMIN_WHATSAPP || []).map(n =>
        TWILIO_WA_CONTENT_SID
          ? sendWhatsAppTemplate(n, TWILIO_WA_CONTENT_SID, { "1": title, "2": "ipfs missing" })
          : sendWhatsApp(n, text)
      ),
    ].filter(Boolean));
  } catch (e) {
    console.warn('notifyIpfsMissing failed:', String(e).slice(0,200));
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
    'email','email_address','emailaddress','primary_email',
    'contact.email','contact.email_address','contactEmail',
    'business_email','work_email','owner_email'
  );
  if (!email) {
    const arr = pick('emails','contact.emails');
    if (Array.isArray(arr)) {
      for (const e of arr) {
        let s = typeof e === 'string' ? e : (e && typeof e.value === 'string' ? e.value : null);
        if (s) { s = s.replace(/^mailto:/i,'').trim(); if (emailRe.test(s)) { email = s; break; } }
      }
    }
  }
  if (!email) {
    for (const v of flatMap.values()) {
      if (typeof v === 'string') {
        const s = v.replace(/^mailto:/i,'').trim();
        if (emailRe.test(s)) { email = s; break; }
      }
    }
  }

  // -------- PHONE / WEBSITE ----------
  const phone   = pick('phone','phone_number','contact.phone','contact.phone_number','mobile','contact.mobile');
  const website = pick('website','url','site','homepage','contact.website','contact.url');

  // -------- ADDRESS PARTS (now with many more synonyms) ----------
  // direct line1
  let line1 = pick(
    'address1','addr1','line1','line_1','address_line1','address_line_1','addressline1','addr_line1',
    'address.address1','address.addr1','address.line1','address.line_1','address.address_line1','address.addressline1','address.addr_line1'
  );

  // street name variants
  const street = pick(
    'street','street1','streetname','street_name','streetName',
    'road','road_name','roadname','strasse','straße','str',
    'address.street','address.street1','address.streetname','address.street_name','address.streetName',
    'address.road','address.road_name','address.roadname','address.strasse','address.straße','address.str'
  );

  // house/number variants
  const houseNo = pick(
    'house_number','housenumber','houseNo','house_no','houseNumber','house_num','houseno',
    'nr','no','numero','num','hausnummer','hausnr','hnr',
    'address.house_number','address.housenumber','address.houseNo','address.house_no','address.houseNumber','address.house_num','address.houseno',
    'address.nr','address.no','address.numero','address.num','address.hausnummer','address.hausnr','address.hnr'
  );

  if (!line1 && (street || houseNo)) {
    line1 = [street, houseNo].filter(Boolean).join(' ').replace(/\s+/g,' ').trim() || null;
  }

  // city / state / postal / country (synonyms)
  const city       = pick('city','town','locality','address.city','address.town','address.locality');
  const state      = pick('state','region','province','county','address.state','address.region','address.province','address.county');
  const postalCode = pick('postalcode','postal_code','postcode','zip','zip_code','address.postalcode','address.postal_code','address.postcode','address.zip','address.zip_code');
  const country    = pick('country','country_code','address.country','address.country_code');

  // explicit free-text variants we keep as-is
  const explicitText =
    pick('address_text','addresstext','address.freeform','address.text') ||
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
async function extractPdfInfoFromDoc(doc) {
  if (!doc?.url) return { used: false, reason: "no_file" };
  const name = doc.name || "";
  const isPdfName = /\.pdf($|\?)/i.test(name);
  try {
    const buf = await fetchAsBuffer(doc.url);
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

async function waitForPdfInfoFromDoc(doc, { maxMs = 12000, stepMs = 1500 } = {}) {
  const start = Date.now();
  let last = await extractPdfInfoFromDoc(doc);
  if (!doc?.url || last.reason === "not_pdf" || last.reason === "no_file") return last;
  while (!last.used && Date.now() - start < maxMs) {
    if (!["http_error", "no_text_extracted", "pdf_parse_failed"].includes(last.reason || "")) break;
    await new Promise((r) => setTimeout(r, stepMs));
    last = await extractPdfInfoFromDoc(doc);
  }
  return last;
}

// ==============================
// Pinata / IPFS
// ==============================
async function pinataUploadFile(file) {
  if (!PINATA_API_KEY || !PINATA_SECRET_API_KEY) throw new Error("Pinata not configured");
  const form = new FormData();
  const buf = Buffer.isBuffer(file.data) ? file.data : Buffer.from(file.data);
  form.append("file", buf, { filename: file.name, contentType: file.mimetype });
  const { status, body } = await sendRequest(
    "POST",
    "https://api.pinata.cloud/pinning/pinFileToIPFS",
    { ...form.getHeaders(), pinata_api_key: PINATA_API_KEY, pinata_secret_api_key: PINATA_SECRET_API_KEY, Accept: "application/json" },
    form
  );
  const json = JSON.parse(body || "{}");
  if (status < 200 || status >= 300) throw new Error(json?.error || "Pinata error");
  const cid = json.IpfsHash;
  return { cid, url: `https://${PINATA_GATEWAY}/ipfs/${cid}`, size: file.size, name: file.name };
}

async function pinataUploadJson(data) {
  if (!PINATA_API_KEY || !PINATA_SECRET_API_KEY) throw new Error("Pinata not configured");
  const payload = JSON.stringify({ pinataContent: data });
  const { status, body } = await sendRequest(
    "POST",
    "https://api.pinata.cloud/pinning/pinJSONToIPFS",
    {
      "Content-Type": "application/json",
      pinata_api_key: PINATA_API_KEY,
      pinata_secret_api_key: PINATA_SECRET_API_KEY,
      Accept: "application/json",
      "Content-Length": Buffer.byteLength(payload),
    },
    payload
  );
  const json = JSON.parse(body || "{}");
  if (status < 200 || status >= 300) throw new Error(json?.error || "Pinata error");
  const cid = json.IpfsHash;
  return { cid, url: `https://${PINATA_GATEWAY}/ipfs/${cid}` };
}

// --- Check if a CID is still pinned on Pinata (returns true when MISSING/unpinned) ---
async function isMissingOnPinata(cid) {
  if (!cid) return false;

  // We support either a JWT or key/secret (use whichever you already have configured)
  const hasJwt = !!PINATA_JWT;
  const hasKeys = !!PINATA_API_KEY && !!PINATA_SECRET_API_KEY;
  if (!hasJwt && !hasKeys) {
    // Not configured to query Pinata — fall back to 'alive' checks only
    return false;
  }

  const url = `https://api.pinata.cloud/data/pinList?hashContains=${encodeURIComponent(cid)}&status=pinned&pageLimit=1`;

  const headers = { Accept: "application/json" };
  if (hasJwt) {
    headers.Authorization = `Bearer ${PINATA_JWT}`;
  } else {
    headers.pinata_api_key = PINATA_API_KEY;
    headers.pinata_secret_api_key = PINATA_SECRET_API_KEY;
  }

  try {
    const { status, body } = await sendRequest("GET", url, headers);
    if (status < 200 || status >= 300) return false; // treat Pinata API hiccups as "unknown" (don’t flag)
    const json = JSON.parse(body || "{}");
    const rows = json?.rows || json?.items || [];
    // If zero pinned rows returned, consider it unpinned/deleted on Pinata
    return !rows || rows.length === 0;
  } catch {
    return false; // network error => don't flag
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
    const cid  = m[1];
    const rest = m[2] || "";
    const b    = base.replace(/\/+$/, "/");
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
      req.on('timeout', () => { try { req.destroy(); } catch {} resolve(false); });
      req.on('error', () => resolve(false));
      req.end();
    });
  } catch { return false; }
}

async function checkCidAlive(cid) {
  if (!cid) return false;
  // 1) your configured gateway (supports mypinata auth)
  const baseHost = PINATA_GATEWAY.replace(/^https?:\/\//, '');
  const primary = `https://${baseHost}/ipfs/${cid}`;
  const headers = {};
  if (/\.mypinata\.cloud$/i.test(baseHost)) {
    if (PINATA_JWT) headers['Authorization'] = `Bearer ${PINATA_JWT}`;
    if (PINATA_GATEWAY_TOKEN) headers['x-pinata-gateway-token'] = PINATA_GATEWAY_TOKEN;
  }
  if (await headOk(primary, headers)) return true;

  // 2) public fallbacks
  const fallbacks = [
    `${(PINATA_PUBLIC_GATEWAY || 'https://gateway.pinata.cloud/ipfs/').replace(/\/+$/, '/')}${cid}`,
    `https://ipfs.io/ipfs/${cid}`,
    `https://cf-ipfs.com/ipfs/${cid}`,
    `https://dweb.link/ipfs/${cid}`,
  ];
  for (const u of fallbacks) if (await headOk(u)) return true;
  return false;
}

/** Fetch a URL into a Buffer (supports mypinata.cloud auth + public fallbacks) */
async function fetchAsBuffer(urlStr) {
  const orig = String(urlStr);

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
      timeout: 15000
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

  const isDedicated = /\.mypinata\.cloud$/i.test(new URL(orig).hostname);
  const headers = {};

  // If it’s a dedicated Pinata subdomain, send auth if available
  if (isDedicated) {
    if (PINATA_JWT)           headers["Authorization"] = `Bearer ${PINATA_JWT}`;
    if (PINATA_GATEWAY_TOKEN) headers["x-pinata-gateway-token"] = PINATA_GATEWAY_TOKEN;
  }

  // 1) Try original URL (with headers for dedicated gateway)
  try {
    return await tryOnce(orig, headers);
  } catch (e) {
    // 2) Fall back to public gateways
    const candidates = [
      toPublicGateway(orig),
      rewriteToGateway(orig, "https://ipfs.io/ipfs/"),
      rewriteToGateway(orig, "https://cf-ipfs.com/ipfs/"),
      rewriteToGateway(orig, "https://dweb.link/ipfs/"),
    ];
    let lastErr = e;
    for (const u of candidates) {
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
    const actorRole   = req.user?.role || 'vendor';
    const { rows } = await pool.query(
      `INSERT INTO bid_audits (bid_id, actor_wallet, actor_role, changes)
       VALUES ($1,$2,$3,$4)
       RETURNING audit_id`,
      [Number(bidId), actorWallet, actorRole, changes]
    );
    if (typeof enrichAuditRow === 'function') {
      enrichAuditRow(pool, rows[0].audit_id).catch(() => null); // adds ipfs_cid & leaf_hash
    }
  } catch (e) {
    console.warn('writeAudit failed (non-fatal):', String(e).slice(0,200));
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

    try { await fs.unlink(tmp); } catch {}

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
    } catch (_) {}
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
  } catch (_) {}

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

  const city    = rg?.city    || null;
  const state   = rg?.state   || null;
  const country = rg?.country || null;
  const label   = rg?.label || [city, state, country].filter(Boolean).join(", ") || null;

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

  async sendToken(tokenSymbol, toAddress, amount) {
    if (!this.signer) throw new Error("Blockchain not configured");
    const token = TOKENS[tokenSymbol];
    const contract = new ethers.Contract(token.address, ERC20_ABI, this.signer);
    const decimals = await contract.decimals();
    const amt = ethers.utils.parseUnits(amount.toString(), decimals);

    const balance = await contract.balanceOf(this.signer.address);
    if (balance < amt) throw new Error("Insufficient balance");

    const tx = await contract.transfer(toAddress, amt);
    const receipt = await tx.wait();
    if (!receipt.status) throw new Error("Transaction failed");
    return { hash: receipt.hash, amount, token: tokenSymbol };
  }

  async getBalance(tokenSymbol) {
    if (!this.signer) return 0;
    const token = TOKENS[tokenSymbol];
    const contract = new ethers.Contract(token.address, ERC20_ABI, this.signer);
    const balance = await contract.balanceOf(this.signer.address);
    const decimals = await contract.decimals();
    return parseFloat(ethers.utils.formatUnits(balance, decimals));
  }
}

const blockchainService = new BlockchainService();

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
});

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
  doc: Joi.object({
    cid: Joi.string().optional(),
    url: Joi.string().uri().required(),
    name: Joi.string().required(),
    size: Joi.number().optional(),
    mimetype: Joi.string().optional(),
  }).optional().allow(null),
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

async function runAgent2OnBid(bidRow, proposalRow, { promptOverride } = {}) {
  if (!openai) {
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
    pdfInfo = await waitForPdfInfoFromDoc(docObj);
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
    const resp = await openai.chat.completions.create({
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
function verifyJwt(token) {
  try { return jwt.verify(token, JWT_SECRET); }
  catch { return null; }
}

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
    return res.status(403).json({ error: "Forbidden" });
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
      `SELECT status FROM vendor_profiles WHERE lower(wallet_address)=lower($1) LIMIT 1`,
      [addr]
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

// cookie-mode verify (kept for compatibility)
app.post("/auth/verify", async (req, res) => {
  const address = norm(req.body?.address);
  const signature = req.body?.signature;
  if (!address || !signature) return res.status(400).json({ error: "address and signature required" });

  const nonce = getNonce(address);
  if (!nonce) return res.status(400).json({ error: "nonce not found or expired" });

  let recovered;
  try { recovered = ethers.utils.verifyMessage(nonce, signature); }
  catch { return res.status(400).json({ error: "invalid signature" }); }

  if (norm(recovered) !== address) {
    return res.status(401).json({ error: "signature does not match address" });
  }

  const role = isAdminAddress(address) ? "admin" : "vendor";
  const token = signJwt({ sub: address, role });

  res.cookie("auth_token", token, {
    httpOnly: true,
    secure: true,
    sameSite: "none",
    maxAge: 7 * 24 * 3600 * 1000,
  });

  // ⬇️ Auto-seed vendor_profiles row with status='pending' and notify admins on FIRST signup
try {
  const w = (address || '').toLowerCase();
  if (w) {
    const { rows } = await pool.query(
      `INSERT INTO vendor_profiles
         (wallet_address, vendor_name, email, phone, website, address, status, created_at, updated_at)
       VALUES ($1, '', NULL, NULL, NULL, NULL, 'pending', NOW(), NOW())
       ON CONFLICT (wallet_address) DO NOTHING
       RETURNING wallet_address, vendor_name, email, phone`,
      [w]
    );

    // Only on first insert (new vendor) → notify admins
    if (rows.length) {
      notifyVendorSignup({
        wallet: rows[0].wallet_address,
        vendorName: rows[0].vendor_name || '',
        email: rows[0].email || '',
        phone: rows[0].phone || '',
      }).catch(() => null);
    }
  }
} catch (e) {
  console.warn('profile auto-seed failed (non-fatal):', String(e).slice(0,200));
}

  nonces.delete(address);
  res.json({ address, role });
});

// nonce compat for frontend
app.get("/auth/nonce", (req, res) => {
  const address = norm(req.query.address);
  if (!address) return res.status(400).json({ error: "address required" });
  const nonce = `LithiumX login nonce: ${Math.floor(Math.random() * 1e9)}`;
  putNonce(address, nonce);
  res.json({ nonce });
});

// login compat for frontend
app.post("/auth/login", async (req, res) => {
  const address = norm(req.body?.address);
  const signature = req.body?.signature;
  if (!address || !signature) return res.status(400).json({ error: "address and signature required" });

  const nonce = getNonce(address);
  if (!nonce) return res.status(400).json({ error: "nonce not found or expired" });

  let recovered;
  try { recovered = ethers.utils.verifyMessage(nonce, signature); }
  catch { return res.status(400).json({ error: "invalid signature" }); }

  if (norm(recovered) !== address) return res.status(401).json({ error: "signature does not match address" });

  const role = isAdminAddress(address) ? "admin" : "vendor";
  const token = signJwt({ sub: address, role });

  res.cookie("auth_token", token, {
    httpOnly: true,
    secure: true,
    sameSite: "none",
    maxAge: 7 * 24 * 3600 * 1000,
  });

  // ⬇️ Auto-seed vendor_profiles row with status='pending' and notify admins on FIRST signup
try {
  const w = (address || '').toLowerCase();
  if (w) {
    const { rows } = await pool.query(
      `INSERT INTO vendor_profiles
         (wallet_address, vendor_name, email, phone, website, address, status, created_at, updated_at)
       VALUES ($1, '', NULL, NULL, NULL, NULL, 'pending', NOW(), NOW())
       ON CONFLICT (wallet_address) DO NOTHING
       RETURNING wallet_address, vendor_name, email, phone`,
      [w]
    );

    // Only on first insert (new vendor) → notify admins
    if (rows.length) {
      notifyVendorSignup({
        wallet: rows[0].wallet_address,
        vendorName: rows[0].vendor_name || '',
        email: rows[0].email || '',
        phone: rows[0].phone || '',
      }).catch(() => null);
    }
  }
} catch (e) {
  console.warn('profile auto-seed failed (non-fatal):', String(e).slice(0,200));
}

  nonces.delete(address);
  res.json({ token, role });
});

app.get("/auth/role", async (req, res) => {
  try {
    // 1) Primary: req.user set by cookie/Bearer
    if (req.user) {
      const address = String(req.user.sub || '');
      const role = req.user.role;
      let vendorStatus = 'pending';

      if (role === 'vendor' && address) {
        const { rows } = await pool.query(
          `SELECT status FROM vendor_profiles WHERE lower(wallet_address)=lower($1) LIMIT 1`,
          [address]
        );
        vendorStatus = (rows[0]?.status || 'pending').toLowerCase();
      }
      return res.json({ address, role, vendorStatus });
    }

    // 2) Legacy cookie fallback (use unique names to avoid redeclare)
    {
      const legacyToken = req.cookies?.auth_token;
      const legacyUser = legacyToken ? verifyJwt(legacyToken) : null;

      if (legacyUser) {
        const address = String(legacyUser.sub || '');
        const role = legacyUser.role;
        let vendorStatus = 'pending';

        if (role === 'vendor' && address) {
          const { rows } = await pool.query(
            `SELECT status FROM vendor_profiles WHERE lower(wallet_address)=lower($1) LIMIT 1`,
            [address]
          );
          vendorStatus = (rows[0]?.status || 'pending').toLowerCase();
        }
        return res.json({ address, role, vendorStatus });
      }
    }

    // 3) Query fallback (?address=0x...)
    {
      const qAddress = norm(req.query.address);
      if (!qAddress) return res.json({ role: "guest" });

      const role = isAdminAddress(qAddress) ? "admin" : "vendor";
      let vendorStatus = 'pending';

      if (role === 'vendor') {
        const { rows } = await pool.query(
          `SELECT status FROM vendor_profiles WHERE lower(wallet_address)=lower($1) LIMIT 1`,
          [qAddress]
        );
        vendorStatus = (rows[0]?.status || 'pending').toLowerCase();
      }
      return res.json({ address: qAddress, role, vendorStatus });
    }
  } catch (e) {
    console.error('/auth/role error', e);
    return res.status(500).json({ error: 'role_failed' });
  }
});

app.post("/auth/logout", (req, res) => {
  res.clearCookie("auth_token");
  res.json({ ok: true });
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

// --- Helper for /admin/entities routes (match org/email/wallet) ---
function deriveEntityKey(body = {}) {
  const id     = String(body.id || '').trim().toLowerCase();             // optional internal id
  const wallet = String(body.ownerWallet || body.wallet || '').trim().toLowerCase();
  const email  = String(body.contactEmail || body.email || '').trim().toLowerCase();
  const org    = String(body.orgName || body.organization || '').trim().toLowerCase();
  return id || wallet || email || org || null;
}

// ==============================
// Routes — Proposals
// ==============================
app.get("/proposals", async (req, res) => {
  try {
    const status = (req.query.status || "").toLowerCase().trim();
    const includeArchived = String(req.query.includeArchived || "").toLowerCase();

    let q = "SELECT * FROM proposals";
    const params = [];

    if (status) {
      q += " WHERE status=$1";
      params.push(status);
    } else if (!["true", "1", "yes"].includes(includeArchived)) {
      q += " WHERE status != 'archived'";
    }

    q += " ORDER BY created_at DESC";

    const { rows } = await pool.query(q, params);
    res.json(mapRows(rows));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// ==============================
// Admin — “Entities” (operate over proposals by org/email/wallet)
// ==============================

// Archive all proposals for a given org/email/wallet
app.post('/admin/entities/archive', adminGuard, async (req, res) => {
  try {
    const key = deriveEntityKey(req.body);
    if (!key) return res.status(400).json({ error: 'Provide orgName OR contactEmail OR ownerWallet (or id)' });

    const { rowCount } = await pool.query(`
      UPDATE proposals
         SET status = 'archived', updated_at = NOW()
       WHERE COALESCE(LOWER(owner_wallet), LOWER(contact), LOWER(org_name)) = $1
         AND status <> 'archived'
    `, [key]);

    return res.json({ ok: true, affected: rowCount });
  } catch (e) {
    console.error('archive entity error', e);
    return res.status(500).json({ error: 'Failed to archive entity' });
  }
});

// Unarchive (set back to a status, default 'pending')
app.post('/admin/entities/unarchive', adminGuard, async (req, res) => {
  try {
    const key = deriveEntityKey(req.body);
    if (!key) return res.status(400).json({ error: 'Provide orgName OR contactEmail OR ownerWallet (or id)' });

    const toStatus = String(req.body?.toStatus || 'pending').toLowerCase();
    if (!['pending','approved','rejected'].includes(toStatus)) {
      return res.status(400).json({ error: 'Invalid toStatus' });
    }

    const { rowCount } = await pool.query(`
      UPDATE proposals
         SET status = $2, updated_at = NOW()
       WHERE COALESCE(LOWER(owner_wallet), LOWER(contact), LOWER(org_name)) = $1
         AND status = 'archived'
    `, [key, toStatus]);

    return res.json({ ok: true, affected: rowCount, toStatus });
  } catch (e) {
    console.error('unarchive entity error', e);
    return res.status(500).json({ error: 'Failed to unarchive entity' });
  }
});

// Delete proposals for that entity (mode=soft/hard via ?mode=soft|hard)
app.delete('/admin/entities', adminGuard, async (req, res) => {
  try {
    const key = deriveEntityKey(req.body);
    if (!key) return res.status(400).json({ error: 'Provide orgName OR contactEmail OR ownerWallet (or id)' });

    const mode = String(req.query.mode || 'soft').toLowerCase(); // soft | hard
    if (mode === 'hard') {
      const { rowCount } = await pool.query(`
        DELETE FROM proposals
         WHERE COALESCE(LOWER(owner_wallet), LOWER(contact), LOWER(org_name)) = $1
      `, [key]);
      return res.json({ success: true, deleted: rowCount, mode: 'hard' });
    }

    const { rowCount } = await pool.query(`
      UPDATE proposals
         SET status = 'archived', updated_at = NOW()
       WHERE COALESCE(LOWER(owner_wallet), LOWER(contact), LOWER(org_name)) = $1
         AND status <> 'archived'
    `, [key]);

    return res.json({ success: true, archived: rowCount, mode: 'soft' });
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
      WHERE lower(owner_wallet) = lower($1)
    `;
    const params = [wallet];

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
    const { rows } = await pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [ id ]);
    if (!rows[0]) return res.status(404).json({ error: "not found" });
    res.json(toCamel(rows[0]));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.post("/proposals", async (req, res) => {
  try {
    const { error, value } = proposalSchema.validate(req.body);
    if (error) return res.status(400).json({ error: error.message });

    // Submitter identity (if logged in via Web3Auth)
    const ownerWallet = (req.user?.sub || null);
    const ownerEmail  = (value.ownerEmail || null);
    const ownerPhone  = toE164(value.ownerPhone || ""); // normalize for WhatsApp (optional helper)

    const q = `
      INSERT INTO proposals (
        org_name, title, summary, contact, address, city, country, amount_usd, docs, cid, status,
        owner_wallet, owner_email, owner_phone, updated_at
      ) VALUES (
        $1,$2,$3,$4,$5,$6,$7,$8,$9,$10,'pending',
        $11,$12,$13, NOW()
      )
      RETURNING proposal_id, org_name, title, summary, contact, address, city, country,
                amount_usd, docs, cid, status, created_at, owner_wallet, owner_email, owner_phone, updated_at
    `;

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
      value.cid,
      ownerWallet,
      ownerEmail,
      ownerPhone || null,
    ];

    const { rows } = await pool.query(q, vals);
    const row = rows[0];

    // Notify admins + proposer on creation (optional; requires NOTIFY_ENABLED & helper)
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

    const sql = `UPDATE proposals SET ${sets.join(', ')} WHERE proposal_id=$${i} RETURNING *`;
    vals.push(id);

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
      `UPDATE proposals SET status='approved' WHERE proposal_id=$1 RETURNING *`,
      [id]
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
         WHERE proposal_id=$1
       RETURNING *`,
      [id]
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
      `UPDATE proposals SET status='archived' WHERE proposal_id=$1 RETURNING *`,
      [id]
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
      `DELETE FROM proposals WHERE proposal_id=$1`,
      [id]
    );
    if (rowCount === 0) return res.status(404).json({ error: "Proposal not found" });
    res.json({ success: true });
  } catch (err) {
    console.error("Error deleting proposal:", err);
    res.status(500).json({ error: "Failed to delete proposal" });
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
          WHERE proposal_id = $1 AND status <> 'archived'
          ORDER BY bid_id DESC`,
        [pid]
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
          "SELECT * FROM bids WHERE lower(wallet_address)=lower($1) AND proposal_id=$2 ORDER BY bid_id DESC",
          [caller, pid]
        );
        const hydrated = await Promise.all(rows.map(r => overlayPaidFromMp(r, pool)));
        return res.json(mapRows(hydrated));
      } else {
        const { rows } = await pool.query(
          "SELECT * FROM bids WHERE lower(wallet_address)=lower($1) ORDER BY bid_id DESC",
          [caller]
        );
        const hydrated = await Promise.all(rows.map(r => overlayPaidFromMp(r, pool)));
        return res.json(mapRows(hydrated));
      }
    }

    // --- ADMIN (or flag OFF): return all bids, hydrated ---
    if (Number.isFinite(pid)) {
      const { rows } = await pool.query(
        "SELECT * FROM bids WHERE proposal_id=$1 ORDER BY bid_id DESC",
        [pid]
      );
      const hydrated = await Promise.all(rows.map(r => overlayPaidFromMp(r, pool)));
      return res.json(mapRows(hydrated));
    } else {
      const { rows } = await pool.query("SELECT * FROM bids ORDER BY bid_id DESC");
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
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [id]);
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
    const { error, value } = bidSchema.validate(req.body);
    if (error) return res.status(400).json({ error: error.message });

    const insertQ = `
      INSERT INTO bids (proposal_id,vendor_name,price_usd,days,notes,wallet_address,preferred_stablecoin,milestones,doc,status,created_at)
      VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,'pending', NOW())
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
      value.doc ? JSON.stringify(value.doc) : null,
    ];
    const { rows } = await pool.query(insertQ, insertVals);
    const inserted = rows[0];

    // Fetch proposal
    const { rows: pr } = await pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [ inserted.proposal_id ]);
    const prop = pr[0] || null;

    // Inline Agent2 analysis with deadline
    const INLINE_ANALYSIS_DEADLINE_MS = Number(process.env.AGENT2_INLINE_TIMEOUT_MS || 12000);
    const analysis = await withTimeout(
      prop ? runAgent2OnBid(inserted, prop) : Promise.resolve({
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

  await pool.query("UPDATE bids SET ai_analysis=$1 WHERE bid_id=$2", [
  JSON.stringify(analysis),
  inserted.bid_id
]);
inserted.ai_analysis = analysis;

// Load vendor + proposal for notifications
const [{ rows: vp }, { rows: prj }] = await Promise.all([
  pool.query(`SELECT * FROM vendor_profiles WHERE lower(wallet_address)=lower($1)`, [ inserted.wallet_address ]),
  pool.query(`SELECT * FROM proposals WHERE proposal_id=$1`, [ inserted.proposal_id ])
]);
const vendor = vp[0] || null;
const proposal = prj[0] || null;

// Fire-and-forget notifications so the HTTP response isn’t delayed
if (typeof notifyBidSubmitted === "function") {
  notifyBidSubmitted(inserted, proposal, vendor).catch(() => null);
}

/* --- Audit: bid created (anchorable) --- */
try {
  const actorWallet = (req.user && (req.user.address || req.user.sub)) || null;
  const actorRole   = (req.user && req.user.role) || 'vendor';

  const ins = await pool.query(
    `INSERT INTO bid_audits (bid_id, actor_wallet, actor_role, changes)
     VALUES ($1, $2, $3, $4)
     RETURNING audit_id`,
    [ Number(inserted.bid_id ?? inserted.id), actorWallet, actorRole, { created: true } ]
  );

  // Enrich asynchronously: sets ipfs_cid + leaf_hash
  if (typeof enrichAuditRow === 'function') {
    enrichAuditRow(pool, ins.rows[0].audit_id).catch(err =>
      console.error('audit enrich failed (create):', err)
    );
  }
} catch (e) {
  console.warn('create audit failed (non-fatal):', String(e).slice(0,200));
}

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
      `UPDATE bids SET status='approved', updated_at=NOW() WHERE bid_id=$1 RETURNING *`,
      [ id ]
    );
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });
    const bid = rows[0];
    await writeAudit(id, req, { status: { to: 'approved' } });

    // 2) Pull proposal + vendor profile for contacts
    const [{ rows: prjRows }, { rows: vpRows }] = await Promise.all([
      pool.query(`SELECT * FROM proposals WHERE proposal_id=$1`, [ bid.proposal_id ]),
      pool.query(`SELECT * FROM vendor_profiles WHERE LOWER(wallet_address)=LOWER($1)`, [ bid.wallet_address ])
    ]);
    const proposal = prjRows[0] || null;
    const vendor   = vpRows[0] || null;

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
      `UPDATE bids SET status='rejected', updated_at=NOW() WHERE bid_id=$1 RETURNING *`,
      [ id ]
    );
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });
    const bid = rows[0];
    await writeAudit(id, req, { status: { to: 'rejected' }, reason });

    // 2) Pull proposal + vendor profile for contacts
    const [{ rows: prjRows }, { rows: vpRows }] = await Promise.all([
      pool.query(`SELECT * FROM proposals WHERE proposal_id=$1`, [ bid.proposal_id ]),
      pool.query(`SELECT * FROM vendor_profiles WHERE LOWER(wallet_address)=LOWER($1)`, [ bid.wallet_address ])
    ]);
    const proposal = prjRows[0] || null;
    const vendor   = vpRows[0] || null;

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
       WHERE bid_id = $1
       RETURNING *`,
      [id]
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
    const { rowCount } = await pool.query(`DELETE FROM bids WHERE bid_id=$1`, [id]);
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
        WHERE bid_id = $1`,
      [bidId]
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
       WHERE bid_id = $1
   RETURNING *`;
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
enrichAuditRow(pool, ins.rows[0].audit_id).catch(/* ... */);
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
      `SELECT bid_id, milestones, price_usd FROM bids WHERE bid_id=$1`,
      [bidId]
    );
    const current = curRows[0];
    if (!current) return res.status(404).json({ error: "Bid not found" });

    // (Optional) Enforce sum === bid price
    // const sum = norm.reduce((s, m) => s + Number(m.amount || 0), 0);
    // if (Number(current.price_usd) !== sum) {
    //   return res.status(400).json({ error: \`Sum of milestone amounts (\${sum}) must equal bid price (\${current.price_usd})\` });
    // }

    const { rows: upd } = await pool.query(
      `UPDATE bids
         SET milestones = $2::jsonb
       WHERE bid_id = $1
       RETURNING *`,
      [bidId, JSON.stringify(norm)]
    );

 // Audit row
const actorWallet = req.user?.sub || req.user?.address || null;
const actorRole   = req.user?.role || "admin";

const ins = await pool.query(
  `INSERT INTO bid_audits (bid_id, actor_wallet, actor_role, changes)
   VALUES ($1, $2, $3, $4)
   RETURNING audit_id`,
  [bidId, actorWallet, actorRole, { milestones: { from: current.milestones, to: norm } }]
);

// fire-and-forget enrichment (IPFS + hash)
enrichAuditRow(pool, ins.rows[0].audit_id).catch(err =>
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
   LEFT JOIN audit_batches ab ON ab.id = ba.batch_id
   WHERE ba.bid_id = $1
   ORDER BY ba.created_at DESC`,
  [itemId]
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
   WHERE b.proposal_id = $1
   ORDER BY ba.created_at DESC`,
  [itemId]
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
  try {
    const period = req.query.period ? String(req.query.period) : periodIdForDate();
    const out = await anchorPeriod(pool, period);
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
    const out = await finalizeExistingAnchor(pool, period, tx);
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
      `SELECT audit_id, bid_id, created_at,
              (ipfs_cid IS NOT NULL) AS has_ipfs,
              (leaf_hash IS NOT NULL) AS has_leaf
         FROM bid_audits
        WHERE batch_id IS NULL
          AND leaf_hash IS NOT NULL
          AND to_char(created_at AT TIME ZONE 'UTC','YYYY-MM-DD"T"HH24') = $1
        ORDER BY audit_id ASC`,
      [period]
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
      SELECT to_char(created_at AT TIME ZONE 'UTC','YYYY-MM-DD"T"HH24') AS period,
             COUNT(*) AS cnt
      FROM bid_audits
      WHERE leaf_hash IS NOT NULL
        AND batch_id IS NULL
      GROUP BY 1
      ORDER BY 1`;
    const { rows } = await pool.query(q);
    res.json({ ok: true, rows });
  } catch (e) {
    res.status(500).json({ ok: false, error: String(e.message || e) });
  }
});

// GET /admin/anchor/last — last few audits the API can see
app.get('/admin/anchor/last', async (req, res) => {
  try {
    const { rows } = await pool.query(`
      SELECT audit_id, bid_id,
             to_char(created_at AT TIME ZONE 'UTC','YYYY-MM-DD"T"HH24:MI:SS') AS created_utc,
             (ipfs_cid IS NOT NULL) AS has_ipfs,
             (leaf_hash IS NOT NULL) AS has_leaf,
             batch_id
      FROM bid_audits
      ORDER BY audit_id DESC
      LIMIT 10`);
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
        LEFT JOIN audit_batches ab ON ab.id = ba.batch_id
       ORDER BY ba.created_at DESC
       LIMIT $1`, [take]);
    res.set('Cache-Control','no-store');
    res.json(rows);
  } catch (e) {
    res.status(500).json({ error: 'Failed to load recent audit' });
  }
});

app.get('/admin/alerts', adminGuard, async (_req, res) => {
  try {
    const { rows } = await pool.query(`
      SELECT created_at, bid_id, changes
        FROM bid_audits
       WHERE changes ? 'ipfs_missing'
       ORDER BY created_at DESC
       LIMIT 100`);
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

// --- Admin Oversight: single payload for the dashboard ---
app.get('/admin/oversight', adminGuard, async (req, res) => {
  try {
    const out = {
      tiles: { openProofs:0, breachingSla:0, pendingPayouts:{count:0,totalUSD:0}, escrowsLocked:0, p50CycleHours:0, revisionRatePct:0 },
      queue: [], vendors: [], alerts: [], recent: [], payouts: { pending: [], recent: [] }
    };

    // tiles: open proofs & SLA
    {
      const { rows } = await pool.query(`
        SELECT
          COUNT(*) FILTER (WHERE status='pending') AS open_pending,
          COUNT(*) FILTER (WHERE status='pending' AND submitted_at < NOW() - INTERVAL '48 hours') AS breaching
        FROM proofs
      `);
      out.tiles.openProofs   = Number(rows[0].open_pending || 0);
      out.tiles.breachingSla = Number(rows[0].breaching || 0);
    }

    // tiles: pending payouts (ignore orphans)
{
  const { rows } = await pool.query(`
    SELECT
      COUNT(*)::int                            AS count,
      COALESCE(SUM(mp.amount_usd), 0)::numeric AS total_usd
    FROM milestone_payments mp
    WHERE mp.status = 'pending'
      AND EXISTS (SELECT 1 FROM bids b WHERE b.bid_id = mp.bid_id)
  `).catch(() => ({ rows: [{ count: 0, total_usd: 0 }] }));

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
        WHERE status='approved' AND submitted_at IS NOT NULL
      `).catch(() => ({ rows:[{ p50h:0 }] }));
      out.tiles.p50CycleHours = Number(rows[0].p50h || 0);
    }

    // tiles: revision rate
    {
      const { rows } = await pool.query(`
        SELECT
          COUNT(*) FILTER (WHERE status IN ('approved','rejected')) AS decided,
          COUNT(*) FILTER (WHERE status='rejected') AS rej
        FROM proofs
      `).catch(() => ({ rows:[{ decided:0, rej:0 }] }));
      const decided = Number(rows[0].decided||0);
      const rej = Number(rows[0].rej||0);
      out.tiles.revisionRatePct = decided ? Math.round(100*rej/decided) : 0;
    }

    // queue: oldest pending proofs
    {
      const { rows } = await pool.query(`
        SELECT p.proof_id, p.bid_id, p.milestone_index, p.status, p.submitted_at, p.updated_at,
               b.vendor_name, b.wallet_address, b.proposal_id, pr.title AS project
          FROM proofs p
          JOIN bids b       ON b.bid_id=p.bid_id
          JOIN proposals pr ON pr.proposal_id=b.proposal_id
         WHERE p.status='pending'
         ORDER BY p.submitted_at NULLS LAST, p.updated_at NULLS LAST
         LIMIT 50
      `);
      out.queue = rows.map(r => ({
        id: r.proof_id,
        vendor: r.vendor_name || r.wallet_address,
        project: r.project,
        milestone: Number(r.milestone_index)+1,
        ageHours: r.submitted_at ? Math.max(0,(Date.now()-new Date(r.submitted_at).getTime())/3600000) : null,
        status: r.status,
        risk: (r.submitted_at && (Date.now()-new Date(r.submitted_at).getTime()) > 48*3600000) ? 'sla' : null,
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
        GROUP BY b.vendor_name, b.wallet_address
        ORDER BY proofs DESC NULLS LAST, vendor_name ASC
        LIMIT 200
      `);
      out.vendors = rows.map(r => ({
        vendor: r.vendor_name || '(unnamed)',
        wallet: r.wallet_address,
        proofs: Number(r.proofs||0),
        approved: Number(r.approved||0),
        cr: Number(r.cr||0),
        approvalPct: Number(r.proofs||0) ? Math.round(100*Number(r.approved||0)/Number(r.proofs||0)) : 0,
        bids: Number(r.bids||0),
        lastActivity: r.last_activity
      }));
    }

    // alerts: ipfs_missing from bid_audits
    {
      const { rows } = await pool.query(`
        SELECT created_at, bid_id, changes
          FROM bid_audits
         WHERE changes ? 'ipfs_missing'
         ORDER BY created_at DESC
         LIMIT 20
      `);
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
         WHERE status='pending'
         ORDER BY created_at DESC
         LIMIT 20
      `).catch(() => ({ rows: [] }));
      const { rows: rec } = await pool.query(`
        SELECT id, bid_id, milestone_index, amount_usd, released_at
          FROM milestone_payments
         WHERE status='released'
         ORDER BY released_at DESC
         LIMIT 20
      `).catch(() => ({ rows: [] }));
      out.payouts.pending = pend || [];
      out.payouts.recent  = rec  || [];
    }

    // recent audits
    {
      const { rows } = await pool.query(`
        SELECT created_at, actor_role, actor_wallet, changes, bid_id
          FROM bid_audits
         ORDER BY created_at DESC
         LIMIT 50
      `).catch(() => ({ rows: [] }));
      out.recent = rows;
    }

    res.set('Cache-Control','no-store');
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
      WHERE status = 'pending' AND tx_hash IS NOT NULL
    `);

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
            SET status='released', released_at=NOW() 
            WHERE id=$1
          `, [row.id]);

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
      WHERE status='pending' AND safe_tx_hash IS NOT NULL
    `);
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
      const { rows: bids } = await pool.query('SELECT * FROM bids WHERE bid_id=$1', [row.bid_id]);
      const bid = bids[0];
      if (!bid) continue;

      const milestones = Array.isArray(bid.milestones)
        ? bid.milestones
        : JSON.parse(bid.milestones || '[]');

      const idx = Number(row.milestone_index);
      const ms = { ...(milestones[idx] || {}) };
      const iso = new Date().toISOString();

      // ✅ set ALL paid markers the UI checks
      ms.paymentTxHash     = ms.paymentTxHash     || txResp.transactionHash;
      ms.safePaymentTxHash = ms.safePaymentTxHash || row.safe_tx_hash; // keep Safe ref
      ms.paymentDate       = ms.paymentDate       || iso;
      ms.paidAt            = ms.paidAt            || ms.paymentDate;
      ms.paymentPending    = false;
      ms.status            = 'paid';

      milestones[idx] = ms;

      await pool.query(
        'UPDATE bids SET milestones=$1 WHERE bid_id=$2',
        [JSON.stringify(milestones), row.bid_id]
      );

      // --- milestone_payments → released ---
      await pool.query(`
        UPDATE milestone_payments
           SET status='released',
               tx_hash=$2,
               released_at=NOW(),
               amount_usd=COALESCE(amount_usd,$3)
         WHERE id=$1
      `, [row.id, txResp.transactionHash, row.amount_usd]);

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

      updated++;
    }

    return res.json({ ok: true, updated });
  } catch (e) {
    console.error('[reconcile-safe] fatal', e);
    return res.status(500).json({ error: e?.message || String(e) });
  }
});

// Force-finalize a milestone as PAID using an executed on-chain tx hash
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
    const { rows: bids } = await pool.query('SELECT * FROM bids WHERE bid_id=$1', [bidId]);
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

    ms.paymentTxHash  = ms.paymentTxHash || txHash;
    ms.paymentDate    = ms.paymentDate || iso;
    ms.paidAt         = ms.paidAt || ms.paymentDate;
    ms.paymentPending = false;
    ms.status         = 'paid';

    milestones[milestoneIndex] = ms;

    await pool.query('UPDATE bids SET milestones=$1 WHERE bid_id=$2', [JSON.stringify(milestones), bidId]);

    // 4) Update or insert milestone_payments row as released
    const { rowCount } = await pool.query(
      `UPDATE milestone_payments
          SET status='released', tx_hash=$3, released_at=NOW()
        WHERE bid_id=$1 AND milestone_index=$2`,
      [bidId, milestoneIndex, txHash]
    );

    if (rowCount === 0) {
      await pool.query(
        `INSERT INTO milestone_payments
          (bid_id, milestone_index, created_at, tx_hash, status, released_at)
         VALUES ($1,$2,NOW(),$3,'released',NOW())`,
        [bidId, milestoneIndex, txHash]
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
      ORDER BY mp.created_at DESC
    `);

    if (orphans.length === 0) {
      return res.json({ ok: true, deleted: 0, orphans: [] });
    }

    // Delete them
    const { rows: deleted } = await pool.query(`
      DELETE FROM milestone_payments mp
      WHERE NOT EXISTS (SELECT 1 FROM bids b WHERE b.bid_id = mp.bid_id)
      RETURNING mp.id, mp.bid_id, mp.milestone_index, mp.amount_usd, mp.status, mp.created_at
    `);

    return res.json({ ok: true, deleted: deleted.length, orphans: deleted });
  } catch (e) {
    console.error('prune-orphans failed', e);
    return res.status(500).json({ ok: false, error: String(e?.message || e) });
  }
});

// --- IPFS monitor: scans recent CIDs and records "ipfs_missing" once ----------
const MONITOR_MINUTES       = Number(process.env.IPFS_MONITOR_INTERVAL_MIN || 15);  // 0 = disabled
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
      [ r.bid_id, cid ]
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
      [ r.bid_id, payload ]
    );
    if (typeof enrichAuditRow === 'function') enrichAuditRow(pool, ins.rows[0].audit_id).catch(()=>{});

    // Notify admins (best-effort)
    const [{ rows: bRows }, { rows: pRows }] = await Promise.all([
      pool.query('SELECT * FROM bids WHERE bid_id=$1', [ r.bid_id ]),
      pool.query('SELECT p.* FROM bids b JOIN proposals p ON p.proposal_id=b.proposal_id WHERE b.bid_id=$1', [ r.bid_id ])
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
        [ pr.bid_id, cid ]
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
        [ pr.bid_id, payload ]
      );
      if (typeof enrichAuditRow === 'function') enrichAuditRow(pool, ins.rows[0].audit_id).catch(()=>{});

      const [{ rows: bRows }, { rows: pRows }] = await Promise.all([
        pool.query('SELECT * FROM bids WHERE bid_id=$1', [ pr.bid_id ]),
        pool.query('SELECT p.* FROM bids b JOIN proposals p ON p.proposal_id=b.proposal_id WHERE b.bid_id=$1', [ pr.bid_id ])
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

  console.log(`[ipfs-monitor] lookback=${days}d checked=${checked} flagged=${flagged} in ${Date.now()-started}ms`);
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
  setTimeout(() => runIpfsMonitor().catch(()=>{}), 10_000); // first run ~10s after boot
  setInterval(() => runIpfsMonitor().catch(()=>{}), MONITOR_MINUTES * 60 * 1000);
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
      SELECT id, bid_id, milestone_index, amount_usd, safe_tx_hash
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

    const provider = new ethers.providers.JsonRpcProvider(process.env.SEPOLIA_RPC_URL);
    const net = await provider.getNetwork();
    const chainId = Number(net.chainId);
    const txServiceUrl = (process.env.SAFE_TXSERVICE_URL || 'https://safe-transaction-sepolia.safe.global')
      .trim()
      .replace(/\/+$/, '');
    const { default: SafeApiKit } = await import('@safe-global/api-kit');
    const api = new SafeApiKit({
      chainId,
      txServiceUrl,
      apiKey: process.env.SAFE_API_KEY || undefined
    });

    let updated = 0;

    for (const row of pendingTxs) {
      try {
        const txResp = await api.getTransaction(row.safe_tx_hash);
        const executed = txResp?.isExecuted && txResp?.transactionHash;
        if (!executed) continue;

        // 1) finalize milestone_payments
        await pool.query(
          `UPDATE milestone_payments
             SET status='released', tx_hash=$2, released_at=NOW()
           WHERE id=$1`,
          [row.id, txResp.transactionHash]
        );

        // 2) mark PAID on bids.milestones (the UI reads these)
        const { rows: bids } = await pool.query('SELECT milestones FROM bids WHERE bid_id=$1', [row.bid_id]);
        if (!bids[0]) continue;

        const arr = Array.isArray(bids[0].milestones)
          ? bids[0].milestones
          : JSON.parse(bids[0].milestones || '[]');

        const idx = row.milestone_index;
        const ms  = { ...(arr[idx] || {}) };
        const iso = new Date().toISOString();

        // set ALL paid markers your UI checks
        ms.paymentTxHash     = ms.paymentTxHash     || txResp.transactionHash;
        ms.safePaymentTxHash = ms.safePaymentTxHash || row.safe_tx_hash;
        ms.paymentDate       = ms.paymentDate       || iso;
        ms.paidAt            = ms.paidAt            || iso;
        ms.paymentPending    = false;
        ms.status            = 'paid';

        arr[idx] = ms;

        await pool.query('UPDATE bids SET milestones=$1 WHERE bid_id=$2', [JSON.stringify(arr), row.bid_id]);

        // 3) (best-effort) notify
        try {
          const { rows: [proposal] } = await pool.query(
            'SELECT * FROM proposals WHERE proposal_id=(SELECT proposal_id FROM bids WHERE bid_id=$1)',
            [row.bid_id]
          );
          if (proposal && typeof notifyPaymentReleased === 'function') {
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
    setTimeout(() => autoReconcileSafeTransactionsOnce().catch(() => {}), 30_000); // first run after 30s
    setInterval(
      () => autoReconcileSafeTransactionsOnce().catch(() => {}),
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
            waitForPdfInfoFromDoc({ url: pdfFile.url, name: pdfFile.name || 'attachment.pdf', mimetype: 'application/pdf' }),
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
          pdfNote = `PDF extraction failed (${String(e).slice(0,120)})`;
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

Proposal:
- Org: ${proposal.org_name || ""}
- Title: ${proposal.title || ""}
- Summary: ${proposal.summary || ""}
- BudgetUSD: ${proposal.amount_usd ?? 0}

Bid:
- Vendor: ${bid.vendor_name || ""}
- PriceUSD: ${bid.price_usd ?? 0}
- Days: ${bid.days ?? 0}
- Notes: ${bid.notes || ""}

Existing Bid Analysis (may omit proofs):
${ai ? JSON.stringify(ai).slice(0, 2000) : "(none)"}

Submitted Proofs (latest first):
${proofsBlock}

Instruction:
- Answer questions about BOTH the bid and its submitted proofs.
- If the user asks about “the proof”, “attachment”, or “PDF”, base your answer on the Proofs section above.
- If a PDF extract was available, use it; otherwise clearly say that no usable PDF text was available.
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

You CAN analyze the attached images (URLs). You CANNOT browse the web or reverse-image-search; only mention this if asked. Avoid generic disclaimers.

Task: Compare "BEFORE" (proposal) vs "AFTER" (proof) images to assess progress/changes and possible image reuse.

ALWAYS provide:
1) 1–2 sentence conclusion (done/partial/unclear).
2) Bullets with:
   • Evidence (specific visual cues, materials, measurements, signage, timestamps)
   • Differences/Progress (what changed between BEFORE and AFTER)
   • Possible reuse / duplicates (same photo reused, tiny edits, stock-like anomalies)
   • Inconsistencies (lighting/shadows mismatch, warped text, repetitive textures)
   • OCR text (short bullets of visible text)
   • Fit-to-proof (how AFTER matches the proof claim & milestone scope)
   • Next checks (alt angles, close-ups, wider context, side-by-side, clearer doc page, etc.)
   • Confidence [0–1]

Rules:
- Be concrete and cite visible cues.
- If BEFORE is missing but AFTER exists, still analyze plausibility & completeness.
- If AFTER is missing, say so.
- If angles differ, note how that limits certainty.
`.trim();

  const beforeImages = proposalImages.slice(0, 6);
  const afterImages  = imageFiles.slice(0, 6);

  const userVisionContent = [
    { type: 'text', text: `User request: ${lastUserText}\n\nCompare BEFORE (proposal docs) vs AFTER (proofs) images.` },
  ];

  if (beforeImages.length) {
    userVisionContent.push({ type: 'text', text: 'BEFORE (from proposal):' });
    for (const f of beforeImages) userVisionContent.push({ type: 'image_url', image_url: { url: f.url } });
  } else {
    userVisionContent.push({ type: 'text', text: 'BEFORE: (none attached in proposal docs)' });
  }

  if (afterImages.length) {
    userVisionContent.push({ type: 'text', text: 'AFTER (from proofs):' });
    for (const f of afterImages) userVisionContent.push({ type: 'image_url', image_url: { url: f.url } });
  } else {
    userVisionContent.push({ type: 'text', text: 'AFTER: (no proof images found)' });
  }

  userVisionContent.push({ type: 'text', text: `\n\n--- CONTEXT ---\n${systemContext}` });

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
  // Text-only fallback (no images anywhere)
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
    res.write(`data: ERROR ${String(err).slice(0,200)}\n\n`);
    res.write(`data: [DONE]\n\n`);
    res.end();
  } catch {}
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
    const analysis = await runAgent2OnBid(bid, proposal, { promptOverride });

    await pool.query('UPDATE bids SET ai_analysis=$1 WHERE bid_id=$2', [
      JSON.stringify(analysis),
      bidId,
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
app.get("/proofs", async (req, res) => {
  try {
    const bidId = Number(req.query.bidId);
    const proposalId = Number(req.query.proposalId);
    if (!Number.isFinite(bidId) && !Number.isFinite(proposalId)) {
      return res.status(400).json({ error: "Provide bidId or proposalId" });
    }

    let rows;
    if (Number.isFinite(bidId)) {
      ({ rows } = await pool.query(
        `SELECT p.*
           FROM proofs p
          WHERE p.bid_id = $1
          ORDER BY p.proof_id ASC`,
        [bidId]
      ));
    } else {
      ({ rows } = await pool.query(
        `SELECT p.*
           FROM proofs p
           JOIN bids b ON b.bid_id = p.bid_id
          WHERE b.proposal_id = $1
          ORDER BY p.proof_id ASC`,
        [proposalId]
      ));
    }

    // normalize for the frontend
    const out = await Promise.all(rows.map(async r => {
      const o = toCamel(r);
      o.files      = coerceJson(o.files)      || [];
      o.fileMeta   = coerceJson(o.fileMeta)   || [];
      o.aiAnalysis = coerceJson(o.aiAnalysis) || null;
      o.geo        = await buildSafeGeoForProof(o); // safe city/state/country (+rounded coords)
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

    const { rows: cur } = await pool.query(`SELECT * FROM proofs WHERE proof_id=$1`, [id]);
    const proof = cur[0];
    if (!proof) return res.status(404).json({ error: "Proof not found" });

    const { rows: upd } = await pool.query(
      `UPDATE proofs
          SET status='approved', approved_at=NOW(), updated_at=NOW()
        WHERE proof_id=$1
      RETURNING *`,
      [id]
    );
    const updated = upd[0];

    await writeAudit(Number(proof.bid_id), req, {
      proof_approved: { proofId: id, index: Number(proof.milestone_index) }
    });

    // notify
    const [{ rows: bRows }, { rows: pRows }] = await Promise.all([
      pool.query(`SELECT * FROM bids WHERE bid_id=$1`, [ proof.bid_id ]),
      pool.query(`SELECT * FROM proposals WHERE proposal_id=(SELECT proposal_id FROM bids WHERE bid_id=$1)`, [ proof.bid_id ])
    ]);
    if (typeof notifyProofApproved === "function") {
      const bid = bRows[0]; const proposal = pRows[0];
      const msIndex = Number(updated.milestone_index) + 1;
      notifyProofApproved({ proof: updated, bid, proposal, msIndex }).catch(() => {});
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

    const { rows: cur } = await pool.query(`SELECT * FROM proofs WHERE proof_id=$1`, [id]);
    const proof = cur[0];
    if (!proof) return res.status(404).json({ error: "Proof not found" });

    const { rows: upd } = await pool.query(
      `UPDATE proofs
          SET status='rejected', updated_at=NOW()
        WHERE proof_id=$1
      RETURNING *`,
      [id]
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
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [ bidId ]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });

    const bid = rows[0];
    const milestones = Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || "[]");
    if (!milestones[idx]) return res.status(400).json({ error: "Invalid index" });

    milestones[idx].completed = true;
    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [ JSON.stringify(milestones), bidId ]);
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
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [ bidId ]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });

    const bid = rows[0];
    const milestones = Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || "[]");
    if (!milestones[milestoneIndex]) return res.status(400).json({ error: "Milestone index out of range" });

    const ms = milestones[milestoneIndex];
    ms.completed = true;
    ms.completionDate = new Date().toISOString();
    if (typeof proof === "string" && proof.trim()) ms.proof = proof.trim();

    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [ JSON.stringify(milestones), bidId ]);
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
          [ bidId, milestoneIndex ]
        );
        const latest = proofs[0];

        // 2) If present and not already approved, flip to approved
        if (latest && String(latest.status || '').toLowerCase() !== 'approved') {
          const { rows: upd } = await pool.query(
            `UPDATE proofs
               SET status = 'approved', updated_at = NOW()
             WHERE proof_id = $1
             RETURNING *`,
            [ latest.proof_id ]
          );
          const updatedProof = upd[0];
          await writeAudit(bidId, req, { proof_approved: { index: milestoneIndex, proofId: updatedProof.proof_id } });

          // 3) Load proposal and fire the existing "proof approved" notifier
          const { rows: [proposal] } =
            await pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [ bid.proposal_id ]);

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
        console.warn("notifyProofApproved via /complete-milestone failed:", String(e).slice(0,200));
      }
    }
    // --- END: approve latest proof for this milestone + notify ---

    const { rows: updated } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [ bidId ]);
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
        created_at      TIMESTAMPTZ NOT NULL DEFAULT now(),
        released_at     TIMESTAMPTZ
      );
      ALTER TABLE milestone_payments
        ADD COLUMN IF NOT EXISTS amount_usd NUMERIC(18,2),
        ADD COLUMN IF NOT EXISTS status TEXT,
        ADD COLUMN IF NOT EXISTS tx_hash TEXT,
        ADD COLUMN IF NOT EXISTS safe_tx_hash TEXT,
        ADD COLUMN IF NOT EXISTS safe_nonce BIGINT,
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
    const { rows: bids } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
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
      `INSERT INTO milestone_payments (bid_id, milestone_index, amount_usd, status, created_at)
       VALUES ($1, $2, $3, 'pending', NOW())
       ON CONFLICT (bid_id, milestone_index) DO NOTHING
       RETURNING id`,
      [bidId, milestoneIndex, msAmountUSD]
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
        const willUseSafe =
          Number(process.env.SAFE_THRESHOLD_USD || 0) > 0 &&
          msAmountUSD >= Number(process.env.SAFE_THRESHOLD_USD || 0) &&
          !!process.env.SAFE_ADDRESS;

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
    const RPC_URL = process.env.SEPOLIA_RPC_URL;
    const SAFE_API_KEY = process.env.SAFE_API_KEY;
    const SAFE_ADDRESS_CS = ethers.utils.getAddress(String(process.env.SAFE_ADDRESS || "").trim()); // checksummed
    const TX_SERVICE_BASE = (process.env.SAFE_TXSERVICE_URL || "https://api.safe.global/tx-service/sep")
      .trim()
      .replace(/\/+$/, "");

    if (!RPC_URL) throw new Error("SEPOLIA_RPC_URL not configured");
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

    // 1) pick a Safe owner key from env
    const rawKeys = (process.env.SAFE_OWNER_KEYS || process.env.PRIVATE_KEYS || "")
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
    const tokenDec  = Number.isInteger(tokenMeta.decimals) ? tokenMeta.decimals : 6;
    if (!tokenAddr) throw new Error(`Unknown token ${token} (no address in TOKENS)`);

    const amountUnits = typeof toTokenUnits === "function"
      ? await toTokenUnits(token, msAmountUSD)
      : ethers.utils.parseUnits(String(msAmountUSD), tokenDec);

    // 4) encode ERC20.transfer(to, amount)
    const erc20Iface = new ethers.utils.Interface(ERC20_ABI);
    const data = erc20Iface.encodeFunctionData("transfer", [ bid.wallet_address, amountUnits ]);
    if (typeof data !== "string" || !data.startsWith("0x")) throw new Error("[SAFE] invalid ERC20.transfer data");

    // 5) EIP-712 typed data (SafeTx)
    const chainId = 11155111; // Sepolia
    const op = 0; // CALL
    const nonceBn = await safeContract.nonce();
    const nonce = ethers.BigNumber.isBigNumber(nonceBn) ? nonceBn.toNumber() : Number(nonceBn);
    if (!Number.isFinite(nonce)) throw new Error("[SAFE] invalid Safe nonce");

    const domain = { chainId, verifyingContract: SAFE_ADDRESS_CS };
    const types = {
      SafeTx: [
        { name: "to",              type: "address" },
        { name: "value",           type: "uint256" },
        { name: "data",            type: "bytes" },
        { name: "operation",       type: "uint8" },
        { name: "safeTxGas",       type: "uint256" },
        { name: "baseGas",         type: "uint256" },
        { name: "gasPrice",        type: "uint256" },
        { name: "gasToken",        type: "address" },
        { name: "refundReceiver",  type: "address" },
        { name: "nonce",           type: "uint256" }
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
          } catch {}
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
          const r = await blockchainService.sendToken(token, bid.wallet_address, msAmountUSD);
          txHash = r?.hash;
        } else {
          txHash = "dev_" + crypto.randomBytes(8).toString("hex");
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
        } catch {}
      } catch (e) {
        console.error("Background pay-milestone failed (left pending)", e);
      }
    }); // <-- single correct closer for setImmediate

    // 5) Return immediately to avoid proxy 502s on slow confirmations
    return res.status(202).json({ ok: true, status: "pending" });

  } catch (err) {
    console.error("pay-milestone error", err);
    const msg = err?.shortMessage || err?.reason || err?.message || "Internal error paying milestone";
    return res.status(500).json({ error: msg });
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
    const { rows: bids } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
    if (!bids[0]) return res.status(404).json({ error: "Bid not found" });
    const bid = bids[0];

    const caller  = String(req.user?.sub || "").toLowerCase();
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
      `SELECT 1 FROM proofs WHERE bid_id=$1 AND milestone_index=$2 AND status='pending' LIMIT 1`,
      [bidId, milestoneIndex]
    );
    if (pend.length) {
      return res.status(409).json({ error: "A proof is already pending review for this milestone." });
    }
    const { rows: lastRows } = await pool.query(
      `SELECT status
         FROM proofs
        WHERE bid_id=$1 AND milestone_index=$2
        ORDER BY submitted_at DESC NULLS LAST,
                 updated_at  DESC NULLS LAST,
                 proof_id    DESC
        LIMIT 1`,
      [bidId, milestoneIndex]
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
  try { rgeo = await reverseGeocode(gpsLat, gpsLon); } catch {}
}

    const legacyText   = (value.proof || "").trim();
    const description  = (value.description || legacyText || "").trim();
    const title        = (value.title || `Proof for Milestone ${milestoneIndex + 1}`).trim();
    const vendorPrompt = (value.vendorPrompt || value.prompt || "").trim();

    // 5) Insert proof row
    const insertQ = `
      INSERT INTO proofs
        (bid_id, milestone_index, vendor_name, wallet_address, title, description,
         files, file_meta, gps_lat, gps_lon, gps_alt, capture_time,
         status, submitted_at, vendor_prompt, updated_at)
      VALUES
        ($1,$2,$3,$4,$5,$6,
         $7,$8,$9,$10,$11,$12,
         'pending', NOW(), $13, NOW())
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
    ];
    const { rows: pr } = await pool.query(insertQ, insertVals);
    let proofRow = pr[0];
    await writeAudit(bidId, req, {
  proof_submitted: {
    index: milestoneIndex,
    proofId: proofRow.proof_id,
    files: (files || []).length,
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
      WHERE b.proposal_id = $1
      ORDER BY p.submitted_at ASC NULLS LAST, p.proof_id ASC`,
      [proposalId]
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
        `SELECT bid_id FROM bids WHERE proposal_id=$1 ORDER BY created_at DESC LIMIT 1`,
        [proposalId]
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
    const where  = Number.isFinite(bidId) ? "WHERE bid_id = $1" : "";
    if (Number.isFinite(bidId)) params.push(bidId);

    const order  = "ORDER BY proof_id DESC";
    const sql    = [baseSql, where, order].filter(Boolean).join("\n");

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
      "SELECT * FROM proofs WHERE bid_id=$1 AND status != 'rejected' ORDER BY submitted_at DESC NULLS LAST",
      [ req.params.bidId ]
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
    const idx   = Number(req.params.milestoneIndex);

    if (!Number.isInteger(bidId) || !Number.isInteger(idx)) {
      return res.status(400).json({ error: "Invalid bidId or milestoneIndex" });
    }

    // Always pick the latest by proof_id (most robust)
    const { rows: proofs } = await pool.query(
      `SELECT *
         FROM proofs
        WHERE bid_id = $1 AND milestone_index = $2
        ORDER BY proof_id DESC
        LIMIT 1`,
      [bidId, idx]
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
        WHERE proof_id = $1
        RETURNING *`,
      [latest.proof_id]
    );
    const updated = rows[0];
    await writeAudit(bidId, req, { proof_approved: { index: idx, proofId: updated.proof_id } });

    // Notify (admins + vendor) if enabled
    if (NOTIFY_ENABLED) {
      try {
        const { rows: [bid] } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [ bidId ]);
        if (bid) {
          const { rows: [proposal] } = await pool.query(
            "SELECT * FROM proposals WHERE proposal_id=$1",
            [ bid.proposal_id ]
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
        console.warn("notifyProofApproved failed (non-fatal):", String(e).slice(0,200));
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
    const idx   = Number(req.params.milestoneIndex);
    const reason = String(req.body?.reason || req.body?.message || req.body?.note || '').trim() || null;

    if (!Number.isInteger(bidId) || !Number.isInteger(idx)) {
      return res.status(400).json({ error: "Invalid bidId or milestoneIndex" });
    }

    // Flip the LATEST proof for this (bid, milestone) to rejected
    const { rows } = await pool.query(`
      WITH latest AS (
        SELECT proof_id
          FROM proofs
         WHERE bid_id = $1 AND milestone_index = $2
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
    `, [bidId, idx]);

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
          [ bid.proposal_id || bid.proposalId ]
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
          [ (bid.wallet_address || "").toLowerCase() ]
        );
        const vp = vprows[0] || {};
        const vendorEmail = (vp.email || "").trim();
        const vendorPhone = (vp.phone || "").trim();
        const vendorTg    = (vp.telegram_chat_id || "").trim();

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
      console.warn("notify-on-reject (proofs route) failed:", String(e).slice(0,200));
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
      'createDate','CreateDate',
      'dateTimeOriginal','DateTimeOriginal',
      'modifyDate','ModifyDate',
      'dateTime','DateTime'
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
        WHERE bid_id = $1
      )
      SELECT milestone_index, status
      FROM ranked
      WHERE rn = 1
    `, [bidId]);

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
    const { rows: pr } = await pool.query('SELECT * FROM proofs WHERE proof_id=$1', [proofId]);
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
  try { rgeo = await reverseGeocode(lat, lon); } catch {}
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
    address:  rgeo.label || rgeo.displayName || null,
    country:  rgeo.country ?? null,
    state:    rgeo.state || rgeo.region || null,
    county:   rgeo.county || rgeo.province || null,
    city:     rgeo.city || rgeo.municipality || null,
    suburb:   rgeo.suburb ?? null,
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
         WHERE bid_id = $1 AND milestone_index = $2
         ORDER BY submitted_at DESC NULLS LAST, updated_at DESC NULLS LAST
         LIMIT 1`,
      [bidId, idx]
    );
    if (!proofs.length) return res.status(404).json({ error: "No proof found for this milestone" });

    const proofId = proofs[0].proof_id;

    // Mark as rejected
    const { rows } = await pool.query(
      `UPDATE proofs
         SET status = 'rejected', updated_at = NOW()
       WHERE proof_id = $1
       RETURNING proof_id, bid_id, milestone_index, status, updated_at`,
      [proofId]
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
      [ bid.proposal_id || bid.proposalId ]
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
      [ (bid.wallet_address || "").toLowerCase() ]
    );
    const vp = vprows[0] || {};
    const vendorEmail = (vp.email || "").trim();
    const vendorPhone = (vp.phone || "").trim();
    const vendorTg    = (vp.telegram_chat_id || "").trim();

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
  console.warn("notify-on-reject failed (non-fatal):", String(e).slice(0,200));
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
        WHERE p.proof_id = $1`,
      [proofId]
    );
    const pr = rows[0];
    if (!pr) return res.status(404).json({ error: 'Proof not found' });

    const caller  = String(req.user?.sub || '').toLowerCase();
    const isAdmin = String(req.user?.role || '').toLowerCase() === 'admin';
    const owner   = String(pr.bid_wallet || '').toLowerCase();

    if (!isAdmin && !caller) return res.status(401).json({ error: 'Unauthorized' });
    if (!isAdmin && caller !== owner) return res.status(403).json({ error: 'Forbidden' });

    if (String(pr.status || '').toLowerCase() === 'archived') {
      return res.json({ ok: true, proof: toCamel(pr) });
    }

    const { rows: upd } = await pool.query(
      `UPDATE proofs
          SET status = 'archived', updated_at = NOW()
        WHERE proof_id = $1
        RETURNING *`,
      [proofId]
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
    const { rows: pr } = await pool.query('SELECT * FROM proofs WHERE proof_id=$1', [proofId]);
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
let pdfText = '';
for (const f of files) {
  if (!f?.url) continue;
  const info = await waitForPdfInfoFromDoc({ url: f.url, name: f.name || '' });
  if (info.used && info.text) {
    pdfText += `\n\n[${f.name || 'file'}]\n${info.text}`;
  }
}
pdfText = pdfText.trim();

// === C) Build location block from AI geo or GPS (+ reverse geocode) ===
let aiGeo = null;
try { aiGeo = JSON.parse(proof?.ai_analysis || '{}')?.geo || null; } catch {}

const lat = Number.isFinite(aiGeo?.lat) ? Number(aiGeo.lat)
          : (Number.isFinite(proof?.gps_lat) ? Number(proof.gps_lat) : null);
const lon = Number.isFinite(aiGeo?.lon) ? Number(aiGeo.lon)
          : (Number.isFinite(proof?.gps_lon) ? Number(proof.gps_lon) : null);

let rgeo = null;
if (Number.isFinite(lat) && Number.isFinite(lon)) {
  try { rgeo = await reverseGeocode(lat, lon); } catch {}
}

const loc = {
  lat, lon,
  country:  aiGeo?.country  ?? rgeo?.country  ?? null,
  state:    aiGeo?.state    ?? rgeo?.state    ?? null,
  county:   aiGeo?.county   ?? rgeo?.county   ?? null,
  city:     aiGeo?.city     ?? rgeo?.city     ?? null,
  suburb:   aiGeo?.suburb   ?? rgeo?.suburb   ?? null,
  postcode: aiGeo?.postcode ?? rgeo?.postcode ?? null,
  address:  aiGeo?.address  ?? rgeo?.displayName ?? rgeo?.label ?? null,
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

    // 5) Choose vision vs text model
    let stream;
    if (hasAnyImages) {
      const beforeImgs = proposalImages.slice(0, 6);
      const afterImgs  = proofImages.slice(0, 6);

      const systemMsg = `
You are Agent2 for LithiumX.

You CAN analyze the attached images (URLs). You CANNOT browse the web or reverse-image-search.

Task: Compare "BEFORE" (proposal) vs "AFTER" (proof) images to assess progress/changes and possible image reuse.

ALWAYS provide:
1) 1–2 sentence conclusion (done/partial/unclear).
2) Bullets with:
   • Evidence (visual cues, materials, measurements, signage, timestamps)
   • Differences/Progress
   • Possible reuse/duplicates
   • Inconsistencies (warped text/repetitive textures)
   • OCR snippets (short)
   • Fit-to-proof (does AFTER match the milestone claim?)
   • Next checks
   • Confidence [0–1]

Be concrete and cite visible cues.`.trim();

      const content = [
        { type: 'text', text: `User request: ${userText}\n\nCompare BEFORE (proposal docs) vs AFTER (proof) images.` },
      ];

      if (beforeImgs.length) {
        content.push({ type: 'text', text: 'BEFORE (from proposal):' });
        for (const f of beforeImgs) content.push({ type: 'image_url', image_url: { url: f.url } });
      } else {
        content.push({ type: 'text', text: 'BEFORE: (none)' });
      }

      if (afterImgs.length) {
        content.push({ type: 'text', text: 'AFTER (from proof):' });
        for (const f of afterImgs) content.push({ type: 'image_url', image_url: { url: f.url } });
      } else {
        content.push({ type: 'text', text: 'AFTER: (none)' });
      }

      content.push({ type: 'text', text: `\n\n--- CONTEXT ---\n${context}` });

      stream = await openai.chat.completions.create({
        model: 'gpt-4o-mini',
        temperature: 0.2,
        stream: true,
        messages: [
          { role: 'system', content: systemMsg },
          { role: 'user', content },
        ],
      });
    } else {
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
      res.write(`data: ERROR ${String(err).slice(0,200)}\n\n`);
      res.write(`data: [DONE]\n\n`);
      res.end();
    } catch {}
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

app.get('/vendor/profile', authRequired, async (req, res) => {
  try {
    const wallet = String(req.user?.sub || '').toLowerCase();
    const { rows } = await pool.query(
      `SELECT wallet_address, vendor_name, email, phone, address, website, telegram_chat_id
       FROM vendor_profiles
       WHERE lower(wallet_address)=lower($1)`,
      [wallet]
    );

    if (!rows[0]) return res.json(null);

    const r = rows[0];

    // address can be JSON or plain text -> normalize to the UI shape you expect
    let parsed = null;
    try { parsed = JSON.parse(r.address || ''); } catch {}
    const address =
      parsed && typeof parsed === 'object'
        ? {
            line1: parsed.line1 || '',
            city: parsed.city || '',
            postalCode: parsed.postalCode || parsed.postal_code || '',
            country: parsed.country || '',
          }
        : {
            line1: r.address || '',
            city: '',
            postalCode: '',
            country: '',
          };

    res.json({
      walletAddress: r.wallet_address,
      vendorName: r.vendor_name || '',
      email: r.email || '',
      phone: r.phone || '',
      website: r.website || '',
      address,
      telegram_chat_id: r.telegram_chat_id || null, // snake_case (backend)
      telegramChatId: r.telegram_chat_id || null,   // camelCase (frontend convenience)
    });
  } catch (e) {
    console.error('GET /vendor/profile error:', e);
    res.status(500).json({ error: 'Failed to load profile' });
  }
});

app.post('/vendor/profile', authRequired, async (req, res) => {
  const wallet = String(req.user?.sub || '').toLowerCase();
  const { error, value } = profileSchema.validate(req.body || {}, { abortEarly: false });
  if (error) return res.status(400).json({ error: error.message });

  // normalize website (add https:// if missing)
  const rawWebsite = (value.website || '').trim();
  const website = rawWebsite && !/^https?:\/\//i.test(rawWebsite) ? `https://${rawWebsite}` : rawWebsite;

  // normalize address: if object, keep JSON + also a flat display line
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
    addressText = [addressJson.line1, addressJson.city, addressJson.postalCode, addressJson.country]
      .filter(Boolean)
      .join(', ');
  }

  // store address as JSON if object given; otherwise plain text
  const addressToStore = addressJson ? JSON.stringify(addressJson) : addressText;

  try {
    const { rows } = await pool.query(
      `INSERT INTO vendor_profiles
         (wallet_address, vendor_name, email, phone, address, website, created_at, updated_at)
       VALUES
         ($1,$2,$3,$4,$5,$6, now(), now())
       ON CONFLICT (wallet_address) DO UPDATE SET
         vendor_name = EXCLUDED.vendor_name,
         email       = EXCLUDED.email,
         phone       = EXCLUDED.phone,
         address     = EXCLUDED.address,
         website     = EXCLUDED.website,
         updated_at  = now()
       RETURNING wallet_address, vendor_name, email, phone, address, website`,
      [wallet, value.vendorName, value.email || null, value.phone || null, addressToStore, website || null]
    );

    // echo back using the same GET shape
    const r = rows[0];
    let parsed = null;
    try { parsed = JSON.parse(r.address || ''); } catch {}
    const address =
      parsed && typeof parsed === 'object'
        ? {
            line1: parsed.line1 || '',
            city: parsed.city || '',
            country: parsed.country || '',
            postalCode: parsed.postalCode || parsed.postal_code || '',
          }
        : {
            line1: r.address || '',
            city: '',
            country: '',
            postalCode: '',
          };

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

// Telegram webhook: supports both "/link 0x..." and deep-link "/start link_0x..."
app.post('/tg/webhook', async (req, res) => {
  try {
    const update = req.body || {};

    // Extract chat id + message text
    const chatId = update?.message?.chat?.id || update?.chat?.id || update?.message?.from?.id;
    const textRaw = update?.message?.text || update?.message?.data || update?.message?.caption || "";
    const text = String(textRaw).trim();

    if (!chatId || !text) return res.json({ ok: true });

    // Parse wallet from either:
    // 1) "/link 0xABC..."     (manual)
    // 2) "/start link_0xABC"  (deep link)
    let wallet = "";
    if (/^\/link\s+/i.test(text)) {
      wallet = text.slice(6).trim();
    } else {
      const m = text.match(/^\/start\s+link_(0x[a-fA-F0-9]{40})$/);
      if (m) wallet = m[1];
    }

    // Ignore unrelated messages
    if (!wallet) return res.json({ ok: true });

    // Validate wallet
    if (!/^0x[a-fA-F0-9]{40}$/.test(wallet)) {
      await sendTelegram([String(chatId)], "Send: /link 0xYourWalletAddress");
      return res.json({ ok: true });
    }

    // Store chat id on the vendor profile
    await pool.query(
      `UPDATE vendor_profiles
         SET telegram_chat_id = $1, updated_at = now()
       WHERE lower(wallet_address) = lower($2)`,
      [ String(chatId), wallet.toLowerCase() ]
    );

    // ALSO store on proposals for proposers/entities
    await pool.query(
      `UPDATE proposals
         SET owner_telegram_chat_id = $1, updated_at = now()
       WHERE lower(owner_wallet) = lower($2)`,
      [ String(chatId), wallet.toLowerCase() ]
    );

    // Confirm to the user
    await sendTelegram([String(chatId)], `✅ Telegram linked to ${wallet}`);
    return res.json({ ok: true });
  } catch (_e) {
    // Always 200 so Telegram doesn't retry forever
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
      const { rows } = await pool.query("SELECT * FROM bids ORDER BY created_at DESC NULLS LAST, bid_id DESC");
      return res.json(mapRows(rows));
    }

    // Scope for vendors/guests; require auth when scoping is on
    if (SCOPE_BIDS_FOR_VENDOR) {
      if (!caller) return res.status(401).json({ error: "Unauthorized" });
      const { rows } = await pool.query(
        "SELECT * FROM bids WHERE lower(wallet_address)=lower($1) ORDER BY created_at DESC NULLS LAST, bid_id DESC",
        [caller]
      );
      return res.json(mapRows(rows));
    }

    // Flag OFF: safest default is still to scope to caller if present
    if (caller) {
      const { rows } = await pool.query(
        "SELECT * FROM bids WHERE lower(wallet_address)=lower($1) ORDER BY created_at DESC NULLS LAST, bid_id DESC",
        [caller]
      );
      return res.json(mapRows(rows));
    }

    // If completely unauthenticated and flag OFF, preserve legacy behavior
    const { rows } = await pool.query("SELECT * FROM bids ORDER BY created_at DESC NULLS LAST, bid_id DESC");
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

// ==============================
// Routes — Admin helpers
// ==============================

/** ADMIN: list bids (optional filter by vendor wallet)
 *  GET /admin/bids
 *  GET /admin/bids?vendorWallet=0xabc...
 *  Returns: { items, total, page, pageSize }
 */
app.get('/admin/bids', adminGuard, async (req, res) => {
  try {
    const vendorWallet = (String(req.query.vendorWallet || '').toLowerCase()) || null;
    const page  = Math.max(1, parseInt(String(req.query.page ?? '1'), 10));
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
        COALESCE(p.title, 'Untitled Project') AS project_title
      FROM bids b
      LEFT JOIN proposals p ON p.proposal_id = b.proposal_id
      WHERE ($1::text IS NULL OR LOWER(b.wallet_address) = $1)
      ORDER BY b.created_at DESC NULLS LAST, b.bid_id DESC
      LIMIT $2 OFFSET $3
    `;
    const countSql = `
      SELECT COUNT(*)::int AS cnt
      FROM bids b
      WHERE ($1::text IS NULL OR LOWER(b.wallet_address) = $1)
    `;

    const [list, count] = await Promise.all([
      pool.query(listSql, [vendorWallet, limit, offset]),
      pool.query(countSql, [vendorWallet]),
    ]);

    const items = list.rows.map(r => ({
      id: r.bid_id,
      projectId: r.proposal_id,
      projectTitle: r.project_title,
      vendorWallet: r.vendor_wallet,
      vendorName: r.vendor_name,
      amountUSD: r.price_usd,
      status: r.status,
      createdAt: new Date(r.created_at).toISOString(),
    }));

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
       ORDER BY created_at DESC NULLS LAST, bid_id DESC`
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

// ADMIN: list proposers/entities that submitted proposals
app.get('/admin/proposers', adminGuard, async (req, res) => {
  try {
    const includeArchived = ['true','1','yes'].includes(String(req.query.includeArchived || '').toLowerCase());
    const qRaw = String(req.query.q || '').trim();
    const q = qRaw ? `%${qRaw}%` : null;

    const page  = Math.max(1, parseInt(String(req.query.page ?? '1'), 10));
    const limit = Math.min(200, Math.max(1, parseInt(String(req.query.limit ?? '100'), 10)));
    const offset = (page - 1) * limit;

    const whereParts = [];
    const paramsList = [];
    let p = 0;

    if (!includeArchived) whereParts.push(`status <> 'archived'`);
    if (q) {
      whereParts.push(`(org_name ILIKE $${++p} OR contact ILIKE $${p} OR owner_wallet ILIKE $${p})`);
      paramsList.push(q);
    }
    const whereSql = whereParts.length ? `WHERE ${whereParts.join(' AND ')}` : '';

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
          COUNT(*) AS proposals_count,
          MAX(created_at) AS last_proposal_at,
          COALESCE(SUM(amount_usd),0)::numeric AS total_budget_usd,
          COUNT(*) FILTER (WHERE status='approved') AS approved_count,
          COUNT(*) FILTER (WHERE status='pending')  AS pending_count,
          COUNT(*) FILTER (WHERE status='rejected') AS rejected_count,
          COUNT(*) FILTER (WHERE status='archived') AS archived_count
        FROM base
        GROUP BY entity_key
      ),
      latest_addr AS (
        SELECT DISTINCT ON (entity_key)
          entity_key, addr_display
        FROM base
        WHERE addr_display IS NOT NULL
        ORDER BY entity_key, created_at DESC
      )
      SELECT g.*, la.addr_display
      FROM grp g
      LEFT JOIN latest_addr la USING (entity_key)
      ORDER BY g.last_proposal_at DESC NULLS LAST, g.org_name ASC
      LIMIT $${++p} OFFSET $${++p};
    `;
    const listParams = paramsList.concat([limit, offset]);

    const countSql = `
      WITH base AS (
        SELECT COALESCE(LOWER(owner_wallet), LOWER(contact), LOWER(org_name)) AS entity_key
        FROM proposals
        ${whereSql}
      )
      SELECT COUNT(DISTINCT entity_key)::int AS cnt FROM base;
    `;
    const countParams = paramsList.slice();

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
      proposalsCount: Number(r.proposals_count) || 0,
      totalBudgetUSD: Number(r.total_budget_usd) || 0,
      lastProposalAt: r.last_proposal_at ? new Date(r.last_proposal_at).toISOString() : null,
      statusCounts: {
        approved: Number(r.approved_count) || 0,
        pending:  Number(r.pending_count)  || 0,
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
      `INSERT INTO vendor_profiles (wallet_address, vendor_name, archived, created_at, updated_at)
         VALUES ($1, '', true, now(), now())
       ON CONFLICT (wallet_address) DO UPDATE SET
         archived = true,
         updated_at = now()
       RETURNING wallet_address, vendor_name, archived, updated_at`,
      [wallet]
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
       WHERE lower(wallet_address)=lower($1)
       RETURNING wallet_address, archived`,
      [wallet]
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

    const { rows } = await pool.query(
      `UPDATE vendor_profiles
         SET status='approved', updated_at=now()
       WHERE lower(wallet_address)=lower($1)
       RETURNING wallet_address, vendor_name, email, phone, telegram_chat_id, status`,
      [wallet]
    );
    if (!rows.length) return res.status(404).json({ error: 'Vendor profile not found' });

// notify vendor (optional, fire-and-forget)
const v = rows[0];
const walletStr = String(v.wallet_address || v.walletAddress || '');
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

    const { rows } = await pool.query(
      `UPDATE vendor_profiles
         SET status='rejected', updated_at=now()
       WHERE lower(wallet_address)=lower($1)
       RETURNING wallet_address, vendor_name, email, phone, telegram_chat_id, status`,
      [wallet]
    );
    if (!rows.length) return res.status(404).json({ error: 'Vendor profile not found' });

    // notify vendor (optional, fire-and-forget)
    const v = rows[0];
    const msg = `❌ Your LithiumX vendor account was not approved.${reason ? `\nReason: ${reason}` : ''}\nWallet: ${v.wallet_address}`;
    Promise.allSettled([
      v.telegram_chat_id ? sendTelegram([String(v.telegram_chat_id)], msg) : null,
      v.email ? (async () => {
        const { text, html } = bi(msg, msg);
        await sendEmail([v.email], 'Vendor account not approved', text, html);
      })() : null,
    ]).catch(()=>null);

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
      `DELETE FROM vendor_profiles WHERE lower(wallet_address) = $1`,
      [wallet]
    );
    if (rowCount === 0) return res.status(404).json({ error: 'Vendor profile not found' });

    res.json({ success: true });
  } catch (e) {
    console.error('DELETE /admin/vendors/:wallet error', e);
    res.status(500).json({ error: 'Failed to delete vendor' });
  }
});

/** ADMIN: list vendors (with or without bids), normalized email + rich address (street + house no + city + postal + country) */
app.get('/admin/vendors', adminGuard, async (req, res) => {
  const includeArchived = ['true','1','yes'].includes(String(req.query.includeArchived || '').toLowerCase());

  const sqlBase = `
    WITH agg AS (
      SELECT
        LOWER(b.wallet_address)                                        AS wallet_address,
        COALESCE(MAX(b.vendor_name),'')                                AS vendor_name,
        COUNT(*)::int                                                  AS bids_count,
        MAX(b.created_at)                                              AS last_bid_at,
        COALESCE(SUM(CASE WHEN b.status IN ('approved','completed')
                          THEN b.price_usd ELSE 0 END),0)::numeric     AS total_awarded_usd
      FROM bids b
      GROUP BY LOWER(b.wallet_address)
    )
    -- vendors who have bids
    SELECT
      a.vendor_name                               AS vendor_name,
      a.wallet_address                            AS wallet_address,
      a.bids_count                                AS bids_count,
      a.last_bid_at                               AS last_bid_at,
      a.total_awarded_usd                         AS total_awarded_usd,
      vp.vendor_name                              AS profile_vendor_name,
      vp.email                                    AS email,
      vp.phone                                    AS phone,
      vp.website                                  AS website,
      vp.address                                  AS address_raw,
      vp.archived                                 AS archived
    FROM agg a
    LEFT JOIN vendor_profiles vp
      ON LOWER(vp.wallet_address) = a.wallet_address

    UNION ALL

    -- profiles that have no bids yet
    SELECT
      COALESCE(vp.vendor_name,'')                 AS vendor_name,
      LOWER(vp.wallet_address)                    AS wallet_address,
      0                                           AS bids_count,
      NULL::timestamptz                           AS last_bid_at,
      0::numeric                                  AS total_awarded_usd,
      vp.vendor_name                              AS profile_vendor_name,
      vp.email                                    AS email,
      vp.phone                                    AS phone,
      vp.website                                  AS website,
      vp.address                                  AS address_raw,
      vp.archived                                 AS archived
    FROM vendor_profiles vp
    WHERE NOT EXISTS (
      SELECT 1 FROM bids b WHERE LOWER(b.wallet_address) = LOWER(vp.wallet_address)
    )
  `;

  let sql = `SELECT * FROM (${sqlBase}) s`;
  if (!includeArchived) {
    sql += ` WHERE COALESCE(s.archived, false) = false`;
  }
  sql += ` ORDER BY s.last_bid_at DESC NULLS LAST, s.vendor_name ASC`;

  try {
    const { rows } = await pool.query(sql);
    const norm = (s) => (typeof s === 'string' && s.trim() !== '' ? s.trim() : null);

    const out = rows.map((r) => {
      // address_raw can be JSON or plain text — normalize to parts
      let addrObj = null;
      if (r.address_raw && r.address_raw.trim().startsWith('{')) {
        try { addrObj = JSON.parse(r.address_raw); } catch { addrObj = null; }
      }

      const parts = addrObj && typeof addrObj === 'object'
        ? {
            line1: norm(addrObj.line1),
            city: norm(addrObj.city),
            state: norm(addrObj.state),
            postalCode: norm(addrObj.postalCode) || norm(addrObj.postal_code),
            country: norm(addrObj.country),
          }
        : {
            line1: norm(r.address_raw),
            city: null,
            state: null,
            postalCode: null,
            country: null,
          };

      const flat = [parts.line1, parts.city, parts.postalCode, parts.country]
        .filter(Boolean).join(', ') || null;

      const email   = norm(r.email);
      const phone   = norm(r.phone);
      const website = norm(r.website);

      return {
        // core
        vendorName: r.profile_vendor_name || r.vendor_name || '',
        walletAddress: r.wallet_address || '',
        bidsCount: Number(r.bids_count) || 0,
        lastBidAt: r.last_bid_at,
        totalAwardedUSD: Number(r.total_awarded_usd) || 0,

        // contact
        email,
        contactEmail: email,
        phone,
        website,

        // address (full + parts + explicit street)
        address: flat,
        street: parts.line1 || null,          // <-- explicit street + number
        address1: parts.line1 || flat,
        addressLine1: parts.line1 || flat,
        city: parts.city,
        state: parts.state,
        postalCode: parts.postalCode,
        country: parts.country,

        // nested copies (optional)
        profile: {
          companyName: r.profile_vendor_name ?? (r.vendor_name || null),
          contactName: null,
          email,
          contactEmail: email,
          phone,
          website,
          address: flat,
          addressText: flat,
          street: parts.line1 || null,
          address1: parts.line1 || flat,
          address2: null,
          city: parts.city,
          state: parts.state,
          postalCode: parts.postalCode,
          country: parts.country,
          notes: null,
        },

        contact: {
          email,
          phone,
          street: parts.line1 || null,
          address: flat,
          addressText: flat,
        },

        archived: !!r.archived,
      };
    });

    res.json(out);
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
      `).catch(() => ({ rows:[{ open_pending:0, breaching:0 }] })),
      pool.query(`
        SELECT COUNT(*) AS cnt, COALESCE(SUM(amount_usd),0) AS usd
        FROM milestone_payments
        WHERE status='pending'
      `).catch(() => ({ rows:[{ cnt:0, usd:0 }] })),
      pool.query(`
        SELECT PERCENTILE_CONT(0.5) WITHIN GROUP (
          ORDER BY EXTRACT(EPOCH FROM (updated_at - submitted_at))/3600.0
        ) AS p50h
        FROM proofs
        WHERE status='approved' AND submitted_at IS NOT NULL AND updated_at IS NOT NULL
      `).catch(() => ({ rows:[{ p50h:0 }] })),
      pool.query(`
        SELECT 
          COUNT(*) FILTER (WHERE status IN ('approved','rejected')) AS decided,
          COUNT(*) FILTER (WHERE status='rejected') AS rej
        FROM proofs
      `).catch(() => ({ rows:[{ decided:0, rej:0 }] })),
    ]);

    res.json({
      openProofs: Number(proofs.rows[0].open_pending||0),
      breachingSla: Number(proofs.rows[0].breaching||0),
      pendingPayouts: {
        count: Number(payouts.rows[0].cnt||0),
        totalUSD: Number(payouts.rows[0].usd||0),
      },
      p50CycleHours: Number(p50.rows[0].p50h||0),
      revisionRatePct: (Number(rev.rows[0].decided||0)
        ? Math.round(100*Number(rev.rows[0].rej)/Number(rev.rows[0].decided))
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
       WHERE p.status='pending'
       ORDER BY p.submitted_at NULLS LAST, p.updated_at NULLS LAST
       LIMIT 100
    `);
    res.json(rows.map(r => ({
      id: r.proof_id,                       // ← no “id” column, use proof_id
      vendor: r.vendor_name || r.wallet_address,
      project: r.project,
      milestone: Number(r.milestone_index)+1,
      ageHours: r.submitted_at
        ? Math.max(0, (Date.now()-new Date(r.submitted_at).getTime())/3600000)
        : null,
      status: r.status,
      risk: (r.submitted_at && (Date.now()-new Date(r.submitted_at).getTime()) > 48*3600000) ? 'sla' : null,
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
      GROUP BY b.vendor_name, b.wallet_address
      ORDER BY proofs DESC NULLS LAST, vendor_name ASC
      LIMIT 200
    `);
    res.json(rows.map(r => ({
      vendor: r.vendor_name || '(unnamed)',
      wallet: r.wallet_address,
      proofs: Number(r.proofs||0),
      approved: Number(r.approved||0),
      cr: Number(r.cr||0),
      approvalPct: Number(r.proofs||0)
        ? Math.round(100*Number(r.approved||0)/Number(r.proofs||0))
        : 0,
      bids: Number(r.bids||0),
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
        SELECT id, bid_id, milestone_index, amount_usd, created_at
          FROM milestone_payments
         WHERE status='pending'
         ORDER BY created_at DESC
         LIMIT 50
      `).catch(() => ({ rows: [] })),
      pool.query(`
        SELECT id, bid_id, milestone_index, amount_usd, released_at, tx_hash
          FROM milestone_payments
         WHERE status='released'
         ORDER BY released_at DESC
         LIMIT 50
      `).catch(() => ({ rows: [] })),
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

    const params = [];
    if (hasSince) params.push(since.toISOString());
    params.push(limit);

    const where = hasSince ? 'WHERE ts > $1' : '';
    const limPos = hasSince ? 2 : 1;

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
         WHERE pr.status IN ('approved','rejected')

        UNION ALL
        -- Payments released
        SELECT mp.released_at AS ts, 'payment_released' AS type,
               b.proposal_id, mp.bid_id, mp.milestone_index,
               NULL::text, NULL::text, NULL::text,
               mp.amount_usd, NULL::numeric, 'released'
          FROM milestone_payments mp
          JOIN bids b ON b.bid_id = mp.bid_id
         WHERE mp.released_at IS NOT NULL
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

    const params = [me];
    if (hasSince) params.push(since.toISOString());
    params.push(limit);

    const where = hasSince ? 'WHERE ts > $2' : '';
    const limPos = hasSince ? 3 : 2;

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
         WHERE lower(b.wallet_address) = lower($1)

        UNION ALL
        -- Proposals I own (if any)
        SELECT p.created_at AS ts, 'proposal_submitted' AS type,
               p.proposal_id, NULL::bigint AS bid_id, NULL::int AS milestone_index,
               p.owner_wallet AS actor_wallet,
               p.title AS title, NULL::text AS vendor_name,
               p.amount_usd AS amount_usd, NULL::numeric AS price_usd, p.status AS status
          FROM proposals p
         WHERE lower(p.owner_wallet) = lower($1)

        UNION ALL
        -- My bids
        SELECT b.created_at AS ts, 'bid_submitted' AS type,
               b.proposal_id, b.bid_id, NULL::int,
               b.wallet_address, NULL::text,
               b.vendor_name, NULL::numeric, b.price_usd, b.status
          FROM bids b
         WHERE lower(b.wallet_address) = lower($1)

        UNION ALL
        -- My proofs
        SELECT COALESCE(pr.submitted_at, pr.created_at) AS ts, 'proof_submitted' AS type,
               b.proposal_id, pr.bid_id, pr.milestone_index,
               b.wallet_address, NULL::text, NULL::text,
               NULL::numeric, NULL::numeric, pr.status
          FROM proofs pr
          JOIN bids b ON b.bid_id = pr.bid_id
         WHERE lower(b.wallet_address) = lower($1)

        UNION ALL
        -- Decisions on my proofs
        SELECT pr.updated_at AS ts, 'proof_decision' AS type,
               b.proposal_id, pr.bid_id, pr.milestone_index,
               NULL::text, NULL::text, NULL::text,
               NULL::numeric, NULL::numeric, pr.status
          FROM proofs pr
          JOIN bids b ON b.bid_id = pr.bid_id
         WHERE lower(b.wallet_address) = lower($1)
           AND pr.status IN ('approved','rejected')

        UNION ALL
        -- Payments released to my milestones
        SELECT mp.released_at AS ts, 'payment_released' AS type,
               b.proposal_id, mp.bid_id, mp.milestone_index,
               NULL::text, NULL::text, NULL::text,
               mp.amount_usd, NULL::numeric, 'released'
          FROM milestone_payments mp
          JOIN bids b ON b.bid_id = mp.bid_id
         WHERE lower(b.wallet_address) = lower($1)
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
    `SELECT last_seen_digest FROM user_dashboard_state WHERE lower(wallet_address)=lower($1) LIMIT 1`,
    [me]
  );
  res.json({ lastSeen: rows[0]?.last_seen_digest || null });
});

app.post('/me/dashboard/last-seen', authRequired, async (req, res) => {
  const me = String(req.user?.sub || '').toLowerCase();
  if (!me) return res.status(401).json({ error: 'unauthorized' });
  const t = req.body?.timestamp ? new Date(String(req.body.timestamp)) : new Date();
  if (Number.isNaN(t.getTime())) return res.status(400).json({ error: 'invalid timestamp' });

  await pool.query(
    `INSERT INTO user_dashboard_state (wallet_address, last_seen_digest, updated_at)
     VALUES ($1, $2, now())
     ON CONFLICT (wallet_address) DO UPDATE
       SET last_seen_digest = EXCLUDED.last_seen_digest, updated_at = now()`,
    [me, t.toISOString()]
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
      latest:   'p.created_at DESC',
      oldest:   'p.created_at ASC',
      bids:     'agg_bids_total DESC NULLS LAST',
      paid:     'agg_ms_paid DESC NULLS LAST',
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

    // Bids for this proposal
    const { rows: bidRows } = await pool.query(
      `SELECT bid_id, proposal_id, vendor_name, wallet_address, price_usd, days, notes,
              preferred_stablecoin, milestones, status, created_at, updated_at
         FROM bids
        WHERE proposal_id = $1
        ORDER BY created_at ASC`,
      [id]
    );

    const bidIds = bidRows.map(b => b.bid_id);

// Load proofs for all bids of this project
let proofs = [];
if (bidIds.length) {
  const { rows: proofRows } = await pool.query(
    `SELECT proof_id, bid_id, milestone_index, title, description, status,
            files, file_meta, gps_lat, gps_lon, capture_time, submitted_at, updated_at
       FROM proofs
      WHERE bid_id = ANY($1::bigint[])
      ORDER BY submitted_at ASC`,
    [ bidIds ]
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
    for (const b of bidRows) {
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
          title: m?.name || `Milestone ${idx+1}`,
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
      ...bidRows.map(b => ({ type: 'bid_submitted', at: b.created_at, bid_id: b.bid_id, actor_role: 'vendor', vendor_name: b.vendor_name })),
      ...proofs.map(p => ({ type: 'proof_submitted', at: p.submitted_at, proof_id: p.proof_id, bid_id: p.bid_id, milestone_index: p.milestone_index })),
      ...paymentsActivity
    ].filter(Boolean).sort((a,b) => new Date(a.at).getTime() - new Date(b.at).getTime());

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
        total: bidRows.length,
        approved: bidRows.filter(b => String(b.status).toLowerCase() === 'approved').length,
        items: bidRows // snake_case; your pages can render as-is
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

// ==============================
// Routes — Payments (legacy)
// ==============================
app.post("/payments/release", adminGuard, async (req, res) => {
  try {
    const { bidId, milestoneIndex } = req.body;
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [ bidId ]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });

    const bid = rows[0];
    const milestones = Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || "[]");
    if (!milestones[milestoneIndex]) return res.status(400).json({ error: "Invalid milestone" });

    const ms = milestones[milestoneIndex];
    if (!ms.completed) return res.status(400).json({ error: "Milestone not completed" });

    const receipt = await blockchainService.sendToken(
      bid.preferred_stablecoin,
      bid.wallet_address,
      ms.amount
    );
    res.json({ success: true, receipt });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// ==============================
// Routes — IPFS via Pinata
// ==============================
app.post("/ipfs/upload-file", async (req, res) => {
  try {
    if (!req.files || !req.files.file) return res.status(400).json({ error: "No file uploaded" });
    const file = req.files.file;
    const result = await pinataUploadFile(file);
    res.json(result);
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.post("/ipfs/upload-json", async (req, res) => {
  try {
    const result = await pinataUploadJson(req.body || {});
    res.json(result);
  } catch (err) {
    res.status(500).json({ error: err.message });
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