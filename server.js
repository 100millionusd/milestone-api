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
//   • Manual analyze endpoint for retries
//
// Key UX guarantees we enforce here:
//   1) Creating a bid returns a terminal ai_analysis object in the same response.
//      That means the frontend does NOT need to refresh to see analysis.
//   2) When a PDF doc is attached, we wait up to ~12s trying to fetch & parse it.
//      Regardless of success or failure, the response is terminal
//      (status: "ready" or "error"), so the UI never shows pending forever.
//   3) PDF debug fields (pdfUsed, pdfDebug) explain why a PDF was skipped
//      (e.g., http_error, no_text, parse_failed), which can be surfaced in the UI.
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
//
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
const axios = require("axios");

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

function mapRows(rows) {
  return rows.map(toCamel);
}

function coerceJson(val) {
  if (!val) return null;
  if (typeof val === "string") {
    try { return JSON.parse(val); } catch { return null; }
  }
  return val;
}

/**
 * Perform a generic HTTP(S) request and return { status, body }.
 * Useful for Pinata as we need raw control over headers and body.
 */
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

/**
 * Fetch a URL into a Buffer (binary).
 */
async function fetchAsBuffer(urlStr) {
  return new Promise((resolve, reject) => {
    const u = new URL(urlStr);
    const lib = u.protocol === "https:" ? https : http;
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

/**
 * Promise.race timeout helper that resolves with onTimeout() after ms.
 */
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
    const first5 = buf.slice(0, 5).toString(); // "%PDF-" for real PDFs
    const isPdf = first5 === "%PDF-" || isPdfName || (doc.mimetype || "").toLowerCase().includes("pdf");

    if (!isPdf) {
      return { used: false, reason: "not_pdf", bytes: buf.length, first5 };
    }

    let text = "";
    try {
      const parsed = await pdfParse(buf);
      text = (parsed.text || "").replace(/\s+/g, " ").trim();
    } catch (e) {
      return {
        used: false,
        reason: "pdf_parse_failed",
        bytes: buf.length,
        first5,
        error: String(e).slice(0, 200),
      };
    }

    if (!text) {
      // likely a scanned PDF; pdf-parse has no OCR
      return { used: false, reason: "no_text_extracted", bytes: buf.length, first5 };
    }

    const capped = text.slice(0, 15000); // ~15k chars cap
    return {
      used: true,
      text: capped,
      snippet: capped.slice(0, 400),
      chars: capped.length,
      bytes: buf.length,
      first5,
    };
  } catch (e) {
    return { used: false, reason: "http_error", error: String(e).slice(0, 200) };
  }
}

/**
 * Retry loop for PDFs (gateway warm-up, transient errors)
 */
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
// ========== Agent2 ==========
async function extractPdfInfoFromDoc(doc) {
  if (!doc?.url) return { used: false, reason: "no_file" };

  const name = doc.name || "";
  const isPdfName = /\.pdf($|\?)/i.test(name);

  try {
    const buf = await fetchAsBuffer(doc.url);
    const first5 = buf.slice(0, 5).toString(); // "%PDF-"
    const isPdf =
      first5 === "%PDF-" ||
      isPdfName ||
      (doc.mimetype || "").toLowerCase().includes("pdf");

    if (!isPdf) {
      return { used: false, reason: "not_pdf", bytes: buf.length, first5 };
    }

    let text = "";
    try {
      const parsed = await pdfParse(buf);
      text = (parsed.text || "").replace(/\s+/g, " ").trim();
    } catch (e) {
      return {
        used: false,
        reason: "pdf_parse_failed",
        bytes: buf.length,
        first5,
        error: String(e).slice(0, 200),
      };
    }

    if (!text) {
      return { used: false, reason: "no_text_extracted", bytes: buf.length, first5 };
    }

    const capped = text.slice(0, 15000);
    return {
      used: true,
      text: capped,
      snippet: capped.slice(0, 400),
      chars: capped.length,
      bytes: buf.length,
      first5,
    };
  } catch (e) {
    return { used: false, reason: "http_error", error: String(e).slice(0, 200) };
  }
}

async function waitForPdfInfoFromDoc(doc, { maxMs = 15000, stepMs = 1500 } = {}) {
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
- Milestones: ${JSON.stringify(milestones)}

${pdfInfo.used
  ? `PDF EXTRACT (truncated):\n"""${pdfInfo.text}"""`
  : `NO PDF TEXT AVAILABLE (file not ready, scanned, or missing).`}
`.trim();

  const outputSpec = `
Return JSON with exactly:
{
  "summary": string,
  "risks": string[],
  "fit": "low" | "medium" | "high",
  "milestoneNotes": string[],
  "confidence": number
}
`.trim();

  if (promptOverride && promptOverride.trim()) {
    const hasPlaceholder = promptOverride.includes("{{CONTEXT}}");
    return hasPlaceholder
      ? promptOverride.replace("{{CONTEXT}}", contextBlock) + "\n\n" + outputSpec
      : contextBlock + "\n\nADDITIONAL INSTRUCTIONS\n----------------------\n" + promptOverride + "\n\n" + outputSpec;
  }

  return `
You are Agent2. Analyze this vendor bid for a proposal and return strict JSON.

${contextBlock}

${outputSpec}
`.trim();
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
    const core = JSON.parse(raw);

    return {
      status: "ready",
      ...core,
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
      pdfDebug: { url: docObj?.url || null, reason: "agent2_error", error: String(e).slice(0, 200) },
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
app.get("/proposals", async (_req, res) => {
  try {
    const { rows } = await pool.query("SELECT * FROM proposals ORDER BY created_at DESC");
    res.json(mapRows(rows));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get("/proposals/:id", async (req, res) => {
  try {
    const { rows } = await pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [ req.params.id ]);
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

    const q = `INSERT INTO proposals (org_name,title,summary,contact,address,city,country,amount_usd,docs,cid,status)
               VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,'pending') RETURNING *`;
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

app.post("/proposals/:id/approve", async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid id" });
  try {
    const { rows } = await pool.query(`UPDATE proposals SET status='approved' WHERE proposal_id=$1 RETURNING *`, [ id ]);
    if (!rows[0]) return res.status(404).json({ error: "Proposal not found" });
    res.json(toCamel(rows[0]));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.post("/proposals/:id/reject", async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid id" });
  try {
    const { rows } = await pool.query(`UPDATE proposals SET status='rejected' WHERE proposal_id=$1 RETURNING *`, [ id ]);
    if (!rows[0]) return res.status(404).json({ error: "Proposal not found" });
    res.json(toCamel(rows[0]));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.patch("/proposals/:id", async (req, res) => {
  const id = Number(req.params.id);
  const desired = String(req.body?.status || "").toLowerCase();
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid id" });
  if (!["approved", "rejected"].includes(desired)) {
    return res.status(400).json({ error: 'Invalid status; expected "approved" or "rejected"' });
  }
  try {
    const { rows } = await pool.query(`UPDATE proposals SET status=$2 WHERE proposal_id=$1 RETURNING *`, [ id, desired ]);
    if (!rows[0]) return res.status(404).json({ error: "Proposal not found" });
    res.json(toCamel(rows[0]));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// ==============================
// Routes — Bids
// ==============================
app.get("/bids", async (req, res) => {
  try {
    const pid = Number(req.query.proposalId);
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
    return res.json(toCamel(rows[0]));
  } catch (err) {
    return res.status(500).json({ error: err.message });
  }
});

// Inline analysis on creation — guarantees terminal ai_analysis in response
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

app.post("/bids/:id/approve", async (req, res) => {
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

app.post("/bids/:id/reject", async (req, res) => {
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

app.patch("/bids/:id", async (req, res) => {
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

// Manual analyze/Retry
// ==============================
app.post("/bids/:id/analyze", async (req, res) => {
  const bidId = Number(req.params.id);
  if (!Number.isFinite(bidId)) {
    return res.status(400).json({ error: "Invalid bid id" });
  }

  try {
    // Fetch bid + proposal
    const { rows: [bid] } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
    if (!bid) return res.status(404).json({ error: "Bid not found" });

    const { rows: [proposal] } = await pool.query(
      "SELECT * FROM proposals WHERE proposal_id=$1",
      [bid.proposal_id]
    );
    if (!proposal) return res.status(404).json({ error: "Proposal not found" });

    // Fetch + parse PDF if attached
    let pdfText = null;
    let pdfDebug = null;
    if (bid.doc && bid.doc.url) {
      try {
        const resp = await axios.get(bid.doc.url, { responseType: "arraybuffer" });
        const parsed = await pdfParse(resp.data);
        pdfText = parsed.text || "";
        pdfDebug = {
          url: bid.doc.url,
          name: bid.doc.name,
          bytes: resp.data.byteLength,
          first5: Buffer.from(resp.data).toString("utf8", 0, 5),
          error: null,
        };
        console.log("PDF extracted (first 500):", pdfText.slice(0, 500));
      } catch (err) {
        console.error("PDF parse failed:", err.message);
        pdfDebug = { url: bid.doc.url, name: bid.doc.name, error: err.message };
      }
    }

    // Build analysis prompt
    const systemPrompt = `
You are Agent2. Analyze this vendor bid critically.

Proposal summary:
${proposal?.summary || "(no summary)"}

Vendor: ${bid.vendor_name}
Price (USD): ${bid.price_usd}
Days: ${bid.days}
Notes: ${bid.notes}

Milestones:
${JSON.stringify(bid.milestones || [], null, 2)}

---

IMPORTANT:
- If PDF contents are provided, summarize them under "PDF Insights".
- Assess feasibility, fit, risks, and alignment with the proposal.
- Always state explicitly whether the PDF text was used.

PDF contents:
${pdfText ? pdfText.slice(0, 15000) : "No PDF provided"}
    `;

    // Call OpenAI
    const completion = await openai.chat.completions.create({
      model: "gpt-4o-mini",
      messages: [{ role: "system", content: systemPrompt }],
    });

    const reply = completion.choices[0].message.content;

    const analysis = {
      status: "ready",
      summary: reply,
      pdfUsed: !!pdfText,
      pdfDebug,
    };

    await pool.query(
      "UPDATE bids SET ai_analysis=$1 WHERE bid_id=$2",
      [JSON.stringify(analysis), bidId]
    );

    res.json({ ...bid, aiAnalysis: analysis });
  } catch (err) {
    console.error("Analyze error:", err);
    res.status(500).json({ error: "Failed to analyze bid" });
  }
});

    // Model prompt (forces explicit PDF mention when available)
    const userPrompt = `
You are Agent2. Analyze this vendor bid and return strict JSON with exactly:
{
  "summary": string,
  "risks": string[],
  "fit": "low" | "medium" | "high",
  "milestoneNotes": string[],
  "confidence": number
}

Requirements:
- If PDF text is available, cite it explicitly and briefly quote 1–2 short excerpts (<= 20 words).
- Evaluate feasibility, risks, and alignment with the proposal and milestones.
- Confidence is a number in [0,1].

Proposal:
- Org: ${prop.org_name || ""}
- Title: ${prop.title || ""}
- Summary: ${prop.summary || ""}
- BudgetUSD: ${prop.amount_usd ?? 0}

Bid:
- Vendor: ${bid.vendor_name || ""}
- PriceUSD: ${bid.price_usd ?? 0}
- Days: ${bid.days ?? 0}
- Notes: ${bid.notes || ""}
- Milestones: ${JSON.stringify(milestones)}

${promptOverride ? `Special instructions:\n${promptOverride}\n` : ""}
${pdfText ? `PDF TEXT (truncated ~15k chars):\n"""${pdfText}"""` : "NO PDF TEXT AVAILABLE"}
`.trim();

    const resp = await openai.chat.completions.create({
      model: "gpt-4o-mini",
      temperature: 0.2,
      messages: [{ role: "user", content: userPrompt }],
      response_format: { type: "json_object" },
    });

    const core = JSON.parse(resp.choices?.[0]?.message?.content || "{}");
    const analysis = {
      status: "ready",
      ...core,
      pdfUsed: !!pdfText,
      pdfDebug,
    };

    // Store JSON in ai_analysis
    await pool.query("UPDATE bids SET ai_analysis=$1 WHERE bid_id=$2", [
      JSON.stringify(analysis),
      id,
    ]);

    const { rows: updated } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [id]);
    return res.json(toCamel(updated[0]));
  } catch (err) {
    console.error("analyze bid error:", err);
    return res.status(500).json({ error: "Agent2 error running analysis" });
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

app.post("/bids/:id/pay-milestone", async (req, res) => {
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
// Routes — Proofs
// ==============================
app.post("/proofs", async (req, res) => {
  try {
    const { bidId, proofCid, description } = req.body;
    const q = "INSERT INTO proofs (bid_id,proof_cid,description,submitted_at,status) VALUES ($1,$2,$3,NOW(),'pending') RETURNING *";
    const { rows } = await pool.query(q, [ bidId, proofCid, description ]);
    res.json(toCamel(rows[0]));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get("/proofs", async (_req, res) => {
  try {
    const { rows } = await pool.query("SELECT * FROM proofs ORDER BY submitted_at DESC NULLS LAST");
    res.json(mapRows(rows));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get("/proofs/:bidId", async (req, res) => {
  try {
    const { rows } = await pool.query("SELECT * FROM proofs WHERE bid_id=$1", [ req.params.bidId ]);
    res.json(mapRows(rows));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.post("/proofs/:bidId/:milestoneIndex/approve", async (req, res) => {
  // stub status change if you later store per-proof statuses
  res.json({ ok: true });
});
app.post("/proofs/:bidId/:milestoneIndex/reject", async (req, res) => {
  res.json({ ok: true });
});

// ==============================
// Routes — Vendor helpers
// ==============================
app.get("/vendor/bids", async (_req, res) => {
  try {
    const { rows } = await pool.query("SELECT * FROM bids ORDER BY created_at DESC NULLS LAST, bid_id DESC");
    res.json(mapRows(rows));
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
// Routes — Payments (legacy)
// ==============================
app.post("/payments/release", async (req, res) => {
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
});
