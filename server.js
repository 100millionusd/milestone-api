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
const pdfParse = require("pdf-parse");
const OpenAI = require("openai");

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

// ==============================
/** DB bootstrap — vendor_profiles (create if missing) */
// ==============================
(async () => {
  try {
    await pool.query(`
      CREATE TABLE IF NOT EXISTS vendor_profiles (
        wallet_address  text PRIMARY KEY,
        vendor_name     text NOT NULL,
        email           text,
        phone           text,
        address         text,
        website         text,
        created_at      timestamptz NOT NULL DEFAULT now(),
        updated_at      timestamptz NOT NULL DEFAULT now()
      );
    `);
    await pool.query(`
      CREATE INDEX IF NOT EXISTS idx_vendor_profiles_name
      ON vendor_profiles (lower(vendor_name));
    `);
    console.log('[db] vendor_profiles ready');
  } catch (e) {
    console.error('vendor_profiles init failed:', e);
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

/** Fetch a URL into a Buffer */
async function fetchAsBuffer(urlStr) {
  return new Promise((resolve, reject) => {
    const lib = urlStr.startsWith("https:") ? https : http;
    const req = lib.get(urlStr, (res) => {
      if (res.statusCode && res.statusCode >= 400) {
        return reject(new Error(`HTTP ${res.statusCode} fetching ${urlStr}`));
      }
      const chunks = [];
      res.on("data", (d) => chunks.push(d));
      res.on("end", () => resolve(Buffer.concat(chunks)));
    });
    req.on("error", reject);
  });
}

/** Promise.race timeout helper */
function withTimeout(p, ms, onTimeout) {
  let t;
  const timeoutP = new Promise((resolve) => {
    t = setTimeout(() => resolve(typeof onTimeout === 'function' ? onTimeout() : onTimeout), ms);
  });
  return Promise.race([p, timeoutP]).finally(() => clearTimeout(t));
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

// ==============================
// Blockchain service
// ==============================
class BlockchainService {
  constructor() {
    this.provider = new ethers.JsonRpcProvider(SEPOLIA_RPC_URL);
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
    const amt = ethers.parseUnits(amount.toString(), decimals);

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
    return parseFloat(ethers.formatUnits(balance, decimals));
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
const JWT_SECRET = process.env.JWT_SECRET || "dev_fallback_secret_change_me";
const ENFORCE_JWT_ADMIN = String(process.env.ENFORCE_JWT_ADMIN || "false").toLowerCase() === "true";
const SCOPE_BIDS_FOR_VENDOR = String(process.env.SCOPE_BIDS_FOR_VENDOR || "false").toLowerCase() === "true";

const nonces = new Map(); // addressLower -> nonce

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
  if (req.user.role !== "admin") return res.status(403).json({ error: "Forbidden" });
  next();
}

// Admin or bid owner guard (for /bids/:id/analyze/chat)
async function adminOrBidOwnerGuard(req, res, next) {
  if (req.user?.role === 'admin') return next();
  if (!req.user?.sub) return res.status(401).json({ error: 'Unauthorized' });

  const bidId = Number(req.params.id);
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

// --- Auth endpoints ---
app.post("/auth/nonce", (req, res) => {
  const address = norm(req.body?.address);
  if (!address) return res.status(400).json({ error: "address required" });
  const nonce = `LithiumX login nonce: ${Math.floor(Math.random() * 1e9)}`;
  nonces.set(address, nonce);
  res.json({ nonce });
});

// cookie-mode verify (kept for compatibility)
app.post("/auth/verify", async (req, res) => {
  const address = norm(req.body?.address);
  const signature = req.body?.signature;
  if (!address || !signature) return res.status(400).json({ error: "address and signature required" });

  const nonce = nonces.get(address);
  if (!nonce) return res.status(400).json({ error: "nonce not found or expired" });

  let recovered;
  try { recovered = ethers.verifyMessage(nonce, signature); }
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

  // ⬇️ Auto-seed vendor_profiles row (non-fatal if it fails)
  try {
    const w = (address || '').toLowerCase();
    if (w) {
      await pool.query(
        `INSERT INTO vendor_profiles (wallet_address, vendor_name, created_at, updated_at)
         VALUES ($1, $2, NOW(), NOW())
         ON CONFLICT (wallet_address) DO NOTHING`,
        [w, '']
      );
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
  nonces.set(address, nonce);
  res.json({ nonce });
});

// login compat for frontend
app.post("/auth/login", async (req, res) => {
  const address = norm(req.body?.address);
  const signature = req.body?.signature;
  if (!address || !signature) return res.status(400).json({ error: "address and signature required" });

  const nonce = nonces.get(address);
  if (!nonce) return res.status(400).json({ error: "nonce not found or expired" });

  let recovered;
  try { recovered = ethers.verifyMessage(nonce, signature); }
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

  // ⬇️ Auto-seed vendor_profiles row (non-fatal if it fails)
  try {
    const w = (address || '').toLowerCase();
    if (w) {
      await pool.query(
        `INSERT INTO vendor_profiles (wallet_address, vendor_name, created_at, updated_at)
         VALUES ($1, $2, NOW(), NOW())
         ON CONFLICT (wallet_address) DO NOTHING`,
        [w, '']
      );
    }
  } catch (e) {
    console.warn('profile auto-seed failed (non-fatal):', String(e).slice(0,200));
  }

  nonces.delete(address);
  res.json({ token, role });
});

app.get("/auth/role", (req, res) => {
  const token = req.cookies?.auth_token;
  const user = token ? verifyJwt(token) : null;
  if (user) return res.json({ address: user.sub, role: user.role });

  // fallback (keeps current frontend working)
  const address = norm(req.query.address);
  if (!address) return res.json({ role: "guest" });
  const role = isAdminAddress(address) ? "admin" : "vendor";
  res.json({ address, role });
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

    const q = `
      INSERT INTO proposals (
        org_name, title, summary, contact, address, city, country, amount_usd, docs, cid, status
      ) VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,'pending')
      RETURNING proposal_id, org_name, title, summary, contact, address, city, country, amount_usd, docs, cid, status, created_at
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
    ];
    const { rows } = await pool.query(q, vals);
    res.json(toCamel(rows[0]));
  } catch (err) {
    res.status(500).json({ error: err.message });
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

// Reject proposal
app.post("/proposals/:id/reject", adminGuard, async (req, res) => {
  try {
    const id = Number(req.params.id);
    if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid id" });
    const { rows } = await pool.query(
      `UPDATE proposals SET status='rejected' WHERE proposal_id=$1 RETURNING *`,
      [id]
    );
    if (rows.length === 0) return res.status(404).json({ error: "Proposal not found" });
    res.json(toCamel(rows[0]));
  } catch (err) {
    console.error("Error rejecting proposal:", err);
    res.status(500).json({ error: "Failed to reject proposal" });
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

    // secure scoping when flag ON and caller is not admin
    const role = (req.user?.role || "guest").toLowerCase();
    const caller = (req.user?.sub || "").toLowerCase();

    if (SCOPE_BIDS_FOR_VENDOR && role !== "admin") {
      if (!caller) return res.status(401).json({ error: "Unauthorized" });

      if (Number.isFinite(pid)) {
        const { rows } = await pool.query(
          "SELECT * FROM bids WHERE lower(wallet_address)=lower($1) AND proposal_id=$2 ORDER BY bid_id DESC",
          [caller, pid]
        );
        return res.json(mapRows(rows));
      } else {
        const { rows } = await pool.query(
          "SELECT * FROM bids WHERE lower(wallet_address)=lower($1) ORDER BY bid_id DESC",
          [caller]
        );
        return res.json(mapRows(rows));
      }
    }

    // Admin or flag OFF: existing behavior
    if (Number.isFinite(pid)) {
      const { rows } = await pool.query("SELECT * FROM bids WHERE proposal_id=$1 ORDER BY bid_id DESC", [ pid ]);
      return res.json(mapRows(rows));
    } else {
      const { rows } = await pool.query("SELECT * FROM bids ORDER BY bid_id DESC");
      return res.json(mapRows(rows));
    }
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get("/bids/:id", async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid bid id" });
  try {
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [ id ]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });

    const bid = rows[0];
    const role = (req.user?.role || "guest").toLowerCase();
    const caller = (req.user?.sub || "").toLowerCase();

    // enforce ownership when flag ON and not admin
    if (SCOPE_BIDS_FOR_VENDOR && role !== "admin") {
      if (!caller) return res.status(401).json({ error: "Unauthorized" });
      if ((bid.wallet_address || "").toLowerCase() !== caller) {
        return res.status(403).json({ error: "Forbidden" });
      }
    }

    return res.json(toCamel(bid));
  } catch (err) {
    return res.status(500).json({ error: err.message });
  }
});

// Inline analysis on creation
app.post("/bids", async (req, res) => {
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

    await pool.query("UPDATE bids SET ai_analysis=$1 WHERE bid_id=$2", [ JSON.stringify(analysis), inserted.bid_id ]);
    inserted.ai_analysis = analysis;

    return res.status(201).json(toCamel(inserted));
  } catch (err) {
    console.error("POST /bids error:", err);
    return res.status(500).json({ error: err.message });
  }
});

app.post("/bids/:id/approve", adminGuard, async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid bid id" });
  try {
    const { rows } = await pool.query(`UPDATE bids SET status='approved' WHERE bid_id=$1 RETURNING *`, [ id ]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });
    return res.json(toCamel(rows[0]));
  } catch (err) {
    console.error("approve bid error", err);
    return res.status(500).json({ error: "Internal error approving bid" });
  }
});

app.post("/bids/:id/reject", adminGuard, async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid bid id" });
  try {
    const { rows } = await pool.query(`UPDATE bids SET status='rejected' WHERE bid_id=$1 RETURNING *`, [ id ]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });
    return res.json(toCamel(rows[0]));
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

app.patch("/bids/:id", adminGuard, async (req, res) => {
  const id = Number(req.params.id);
  const desired = String(req.body?.status || "").toLowerCase();
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid bid id" });
  if (!["approved", "rejected"].includes(desired)) {
    return res.status(400).json({ error: 'Invalid status; expected "approved" or "rejected"' });
  }
  try {
    const { rows } = await pool.query(`UPDATE bids SET status=$2 WHERE bid_id=$1 RETURNING *`, [ id, desired ]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });
    return res.json(toCamel(rows[0]));
  } catch (err) {
    console.error("patch bid status error", err);
    return res.status(500).json({ error: "Internal error updating bid status" });
  }
});

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

  const userMessages = Array.isArray(req.body && req.body.messages) ? req.body.messages : [];

  // SSE headers
  res.set({
    'Content-Type': 'text/event-stream; charset=utf-8',
    'Cache-Control': 'no-cache, no-transform',
    'Connection': 'keep-alive',
  });
  if (typeof res.flushHeaders === 'function') res.flushHeaders();

  try {
    const { rows: [bid] } = await pool.query('SELECT * FROM bids WHERE bid_id=$1', [bidId]);
    if (!bid) { res.write(`data: ERROR Bid not found\n\n`); res.write(`data: [DONE]\n\n`); return res.end(); }

    const { rows: [proposal] } = await pool.query('SELECT * FROM proposals WHERE proposal_id=$1', [bid.proposal_id]);
    if (!proposal) { res.write(`data: ERROR Proposal not found\n\n`); res.write(`data: [DONE]\n\n`); return res.end(); }

    const ai = coerceJson(bid.ai_analysis);
    const context =
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

Existing Analysis:
${ai ? JSON.stringify(ai).slice(0, 4000) : "(none)"}

Answer the user's question about this bid/proposal. Keep it concise.`;

    const msgs = [
      { role: 'system', content: context },
      ...userMessages.map((m) => ({
        role: m && m.role === 'assistant' ? 'assistant' : 'user',
        content: String((m && m.content) || ''),
      })),
    ];

    const stream = await openai.chat.completions.create({
      model: 'gpt-4o-mini',
      temperature: 0.2,
      messages: msgs,
      stream: true,
    });

    for await (const part of stream) {
      const token = part && part.choices && part.choices[0] && part.choices[0].delta && part.choices[0].delta.content || '';
      if (token) res.write(`data: ${token}\n\n`);
    }
    res.write(`data: [DONE]\n\n`);
    res.end();
  } catch (err) {
    console.error('Chat error:', err);
    try { res.write(`data: ERROR ${String(err).slice(0,200)}\n\n`); res.write(`data: [DONE]\n\n`); res.end(); } catch {}
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
app.post("/bids/:id/complete-milestone", async (req, res) => {
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

    const { rows: updated } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [ bidId ]);
    return res.json(toCamel(updated[0]));
  } catch (err) {
    console.error("complete-milestone error", err);
    return res.status(500).json({ error: "Internal error completing milestone" });
  }
});

app.post("/bids/:id/pay-milestone", adminGuard, async (req, res) => {
  const bidId = Number(req.params.id);
  const { milestoneIndex } = req.body || {};
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
    if (!ms.completed) return res.status(400).json({ error: "Milestone not completed" });

    const receipt = await blockchainService.sendToken(
      bid.preferred_stablecoin,
      bid.wallet_address,
      ms.amount
    );

    ms.paymentTxHash = receipt.hash;
    ms.paymentDate = new Date().toISOString();

    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [ JSON.stringify(milestones), bidId ]);

    const { rows: updated } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [ bidId ]);
    return res.json({ success: true, bid: toCamel(updated[0]), receipt });
  } catch (err) {
    console.error("pay-milestone error", err);
    return res.status(500).json({ error: "Internal error paying milestone" });
  }
});

// ==============================
// Routes — Proofs (robust, with Agent2)
// ==============================
app.post("/proofs", async (req, res) => {
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
    // accept either name from the client
    prompt: Joi.string().allow("").optional(),
    vendorPrompt: Joi.string().allow("").optional(),
  })
  .or('proof', 'description') // Require either proof OR description
  .messages({
    'object.missing': 'Must provide either proof (legacy) or description (new format)'
  });

  const { error, value } = schema.validate(req.body || {}, { abortEarly: false });
  if (error) return res.status(400).json({ error: error.message });

  const { bidId, milestoneIndex } = value;

  try {
    // 1) Ensure bid exists
    const { rows: bids } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
    if (!bids[0]) return res.status(404).json({ error: "Bid not found" });
    const bid = bids[0];

    // 2) Ensure milestoneIndex is valid
    const milestones = Array.isArray(bid.milestones)
      ? bid.milestones
      : JSON.parse(bid.milestones || "[]");
    if (!milestones[milestoneIndex]) {
      return res.status(400).json({ error: "Invalid milestoneIndex for this bid" });
    }

    // 3) Normalize proof fields
    const files = Array.isArray(value.files) ? value.files : [];
    const legacyText = (value.proof || "").trim();
    const description = (value.description || legacyText || "").trim();
    const title = (value.title || `Proof for Milestone ${milestoneIndex + 1}`).trim();
    const vendorPrompt = (value.vendorPrompt || value.prompt || "").trim();

    // 4) Insert proof row (pending)
    const insertQ = `
      INSERT INTO proofs
        (bid_id, milestone_index, vendor_name, wallet_address, title, description, files, status, submitted_at, vendor_prompt, updated_at)
      VALUES
        ($1,$2,$3,$4,$5,$6,$7,'pending', NOW(), $8, NOW())
      RETURNING *`;
    const insertVals = [
      bidId,
      milestoneIndex,
      bid.vendor_name || bid.vendorName || null,
      bid.wallet_address || bid.walletAddress || null,
      title,
      description,
      JSON.stringify(files),
      vendorPrompt || null,
    ];
    const { rows: pr } = await pool.query(insertQ, insertVals);
    let proofRow = pr[0];

    // 5) Try Agent2 analysis (non-fatal)
    let analysis = null;
    try {
      if (openai && (vendorPrompt || description || files.length)) {
        // pull proposal for context
        const { rows: prj } = await pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [
          bid.proposal_id || bid.proposalId,
        ]);
        const proposal = prj[0] || null;

        const basePrompt = `
You are Agent2. Evaluate a vendor's submitted proof for a specific milestone.

Return strict JSON:
{
  "summary": string,
  "evidence": string[],
  "gaps": string[],
  "fit": "low" | "medium" | "high",
  "confidence": number
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
        `.trim();

        const fullPrompt = vendorPrompt ? `${vendorPrompt}\n\n---\n${basePrompt}` : basePrompt;

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
      } else {
        analysis = {
          summary: "OpenAI not configured; no automatic proof analysis.",
          evidence: [],
          gaps: [],
          fit: "low",
          confidence: 0,
        };
      }
    } catch (e) {
      console.error("Agent2 proof analysis error:", e);
      analysis = { summary: "Agent2 failed during analysis.", evidence: [], gaps: [], fit: "low", confidence: 0 };
    }

    // 6) Save analysis (best-effort)
    try {
      await pool.query("UPDATE proofs SET ai_analysis=$1, updated_at=NOW() WHERE proof_id=$2", [
        JSON.stringify(analysis),
        proofRow.proof_id,
      ]);
      proofRow.ai_analysis = analysis;
    } catch (e) {
      console.error("Failed to save ai_analysis for proof:", e);
    }

    // 7) Also stamp a simple proof note back to the bid milestone for quick view
    const ms = milestones;
    ms[milestoneIndex] = {
      ...(ms[milestoneIndex] || {}),
      proof:
        description ||
        (files.length ? `Files:\n${files.map((f) => f.url).join("\n")}` : "") ||
        legacyText,
    };
    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [JSON.stringify(ms), bidId]);

    // 8) Done
    return res.status(201).json(toCamel(proofRow));
  } catch (err) {
    console.error("POST /proofs error:", err);
    // return a safe 400 with guidance
    return res
      .status(400)
      .json({ error: "Invalid /proofs request. Check bidId, milestoneIndex, and payload format." });
  }
});

app.get("/proofs", adminGuard, async (_req, res) => {
  try {
    const { rows } = await pool.query("SELECT * FROM proofs ORDER BY submitted_at DESC NULLS LAST");
    res.json(mapRows(rows));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get("/proofs/:bidId", adminGuard, async (req, res) => {
  try {
    const { rows } = await pool.query("SELECT * FROM proofs WHERE bid_id=$1 ORDER BY submitted_at DESC NULLS LAST", [ req.params.bidId ]);
    res.json(mapRows(rows));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.post("/proofs/:bidId/:milestoneIndex/approve", adminGuard, async (_req, res) => {
  // stub status change if you later store per-proof statuses
  res.json({ ok: true });
});
app.post("/proofs/:bidId/:milestoneIndex/reject", adminGuard, async (_req, res) => {
  res.json({ ok: true });
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

    // 2) Load bid + proposal for context
    const { rows: br } = await pool.query('SELECT * FROM bids WHERE bid_id=$1', [proof.bid_id]);
    const bid = br[0];
    if (!bid) return res.status(404).json({ error: 'Bid not found for proof' });

    const { rows: por } = await pool.query('SELECT * FROM proposals WHERE proposal_id=$1', [bid.proposal_id]);
    const proposal = por[0] || null;

    // 3) Build prompt
    const vendorPrompt = typeof req.body?.prompt === 'string' ? req.body.prompt.trim() : '';
    const files = Array.isArray(proof.files) ? proof.files : (typeof proof.files === 'string' ? JSON.parse(proof.files || '[]') : []);
    const description = String(proof.description || '').slice(0, 2000);

    const basePrompt = `
You are Agent2. Evaluate a vendor's submitted proof for a specific milestone.

Return strict JSON:
{
  "summary": string,
  "evidence": string[],
  "gaps": string[],
  "fit": "low" | "medium" | "high",
  "confidence": number
}

Context:
- Proposal: ${proposal?.title || "(unknown)"} (${proposal?.org_name || "(unknown)"})
- Milestone: ${(Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || "[]"))[proof.milestone_index]?.name || "(unknown)"} — $${(Array.isArray(bid.milestones) ? bid.milestones : JSON.parse(bid.milestones || "[]"))[proof.milestone_index]?.amount ?? "?"}
- Vendor: ${bid.vendor_name || "(unknown)"}

Proof title: ${proof.title || "(untitled)"}
Proof description (truncated):
"""${description}"""

Files:
${files.map((f) => `- ${f.name || "file"}: ${f.url}`).join("\n") || "(none)"}
    `.trim();

    const fullPrompt = vendorPrompt ? `${vendorPrompt}\n\n---\n${basePrompt}` : basePrompt;

    // 4) Run OpenAI (or fallback)
    let analysis;
    if (!openai) {
      analysis = {
        summary: "OpenAI not configured; no automatic proof analysis.",
        evidence: [],
        gaps: [],
        fit: "low",
        confidence: 0,
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
    }

    // 5) Save & return
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
      `SELECT wallet_address, vendor_name, email, phone, address, website
       FROM vendor_profiles
       WHERE lower(wallet_address)=lower($1)`,
      [wallet]
    );

    if (!rows[0]) return res.json(null);

    const r = rows[0];
    // try to parse address as JSON; otherwise treat as single-line
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

    return res.json({
      walletAddress: r.wallet_address,
      vendorName: r.vendor_name || '',
      email: r.email || '',
      phone: r.phone || '',
      website: r.website || '',
      address,
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
    console.error('GET /admin/bids error:', e);
    res.status(500).json({ error: 'Server error' });
  }
});

/** ADMIN: list vendors (with or without bids), include email/address at top-level and inside profile */
app.get('/admin/vendors', adminGuard, async (req, res) => {
  const enrichedSql = `
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
    SELECT
      a.vendor_name,
      a.wallet_address,
      a.bids_count,
      a.last_bid_at,
      a.total_awarded_usd,
      vp.vendor_name AS profile_vendor_name,
      vp.email       AS email_raw,
      vp.phone       AS phone_raw,
      vp.website     AS website_raw,
      vp.address     AS address_raw
    FROM agg a
    LEFT JOIN vendor_profiles vp
      ON LOWER(vp.wallet_address) = a.wallet_address
    UNION ALL
    -- include vendors that have profile but no bids yet
    SELECT
      COALESCE(vp.vendor_name,'')          AS vendor_name,
      LOWER(vp.wallet_address)             AS wallet_address,
      0                                    AS bids_count,
      NULL::timestamptz                    AS last_bid_at,
      0::numeric                           AS total_awarded_usd,
      vp.vendor_name                       AS profile_vendor_name,
      vp.email                             AS email_raw,
      vp.phone                             AS phone_raw,
      vp.website                           AS website_raw,
      vp.address                           AS address_raw
    FROM vendor_profiles vp
    WHERE NOT EXISTS (
      SELECT 1 FROM bids b WHERE LOWER(b.wallet_address) = LOWER(vp.wallet_address)
    )
    ORDER BY last_bid_at DESC NULLS LAST, vendor_name ASC
  `;

  try {
    const { rows } = await pool.query(enrichedSql);

  const out = rows.map(r => {
  // Parse address (JSON or plain text)
  let addrObj = null;
  if (r.address_raw) {
    try { addrObj = JSON.parse(r.address_raw); } catch { addrObj = null; }
  }

  const normalizedObj = addrObj && typeof addrObj === 'object'
    ? {
        line1: addrObj.line1 || '',
        city: addrObj.city || '',
        postalCode: addrObj.postalCode || addrObj.postal_code || '',
        country: addrObj.country || '',
      }
    : { line1: (r.address_raw || '') };

  const flatAddress = [normalizedObj.line1, normalizedObj.city, normalizedObj.postalCode, normalizedObj.country]
    .filter(Boolean)
    .join(', ') || null;

  const email   = r.email_raw   || null;
  const phone   = r.phone_raw   || null;
  const website = r.website_raw || null;

  return {
    vendorName: r.profile_vendor_name || r.vendor_name || '',
    walletAddress: r.wallet_address || '',
    bidsCount: Number(r.bids_count) || 0,
    lastBidAt: r.last_bid_at,
    totalAwardedUSD: Number(r.total_awarded_usd) || 0,

    // Top-level (flat + aliases)
    email,
    phone,
    website,
    address: flatAddress,
    address1: normalizedObj.line1 || flatAddress || null,
    addressLine1: normalizedObj.line1 || flatAddress || null,
    addressText: flatAddress,
    location: flatAddress,

    // Nested profile (object + flat for any UI)
    profile: {
      companyName: r.profile_vendor_name ?? (r.vendor_name || null),
      contactName: null,
      email,
      phone,
      website,

      // <-- many UIs read this:
      address: normalizedObj,                 // { line1, city, postalCode, country }

      // also provide flat strings/aliases
      addressText: flatAddress,
      address1: normalizedObj.line1 || flatAddress || null,
      addressLine1: normalizedObj.line1 || flatAddress || null,
      city: normalizedObj.city || null,
      state: null,
      postalCode: normalizedObj.postalCode || null,
      country: normalizedObj.country || null,
      notes: null,
    },
  };
});

    res.json(out);
  } catch (e) {
    console.error('admin/vendors error', e);
    res.status(500).json({ error: 'Failed to list vendors' });
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
