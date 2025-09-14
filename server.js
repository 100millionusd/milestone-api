// server.js — Milestone API (Postgres + Blockchain + IPFS + Agent2 + PDF parsing)
// =================================================================================
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

// ========== Config ==========
const PORT = Number(process.env.PORT || 3000);
const DEFAULT_ORIGIN = "https://lithiumx.netlify.app";

const CORS_ORIGINS = (process.env.CORS_ORIGINS || process.env.CORS_ORIGIN || DEFAULT_ORIGIN)
  .split(",")
  .map((s) => s.trim())
  .filter(Boolean);

const PINATA_API_KEY = (process.env.PINATA_API_KEY || "").trim();
const PINATA_SECRET_API_KEY = (process.env.PINATA_SECRET_API_KEY || "").trim();
const PINATA_GATEWAY = process.env.PINATA_GATEWAY_DOMAIN || "gateway.pinata.cloud";

// ✅ OpenAI client (supports project-scoped keys)
const openai = (() => {
  const key = (process.env.OPENAI_API_KEY || "").trim();
  if (!key) return null;
  return new OpenAI({
    apiKey: key,
    project: process.env.OPENAI_PROJECT || undefined,      // set if your key starts with sk-proj-
    organization: process.env.OPENAI_ORG || undefined,     // optional
  });
})();

// Blockchain
const NETWORK = process.env.NETWORK || "sepolia";
const SEPOLIA_RPC_URL = process.env.SEPOLIA_RPC_URL || "https://ethereum-sepolia.publicnode.com";
const PRIVATE_KEY = process.env.PRIVATE_KEY || "";
const ESCROW_ADDR = process.env.ESCROW_ADDR || "";

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

// ========== DB ==========
const pool = new Pool({
  connectionString: process.env.DATABASE_URL,
  ssl: { rejectUnauthorized: false },
});

// ========== CamelCase Mapper ==========
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

// ========== Validation ==========
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

// priceBol removed entirely
const bidSchema = Joi.object({
  proposalId: Joi.number().integer().required(),
  vendorName: Joi.string().required(),
  priceUSD: Joi.number().required(),
  days: Joi.number().integer().required(),
  notes: Joi.string().allow(""),
  walletAddress: Joi.string().pattern(/^0x[a-fA-F0-9]{40}$/).required(),
  preferredStablecoin: Joi.string().valid("USDT", "USDC").default("USDT"),
  milestones: Joi.array()
    .items(
      Joi.object({
        name: Joi.string().required(),
        amount: Joi.number().required(),
        dueDate: Joi.date().iso().required(),
      })
    )
    .min(1)
    .required(),
  doc: Joi.object({
    cid: Joi.string().optional(),
    url: Joi.string().uri().required(),
    name: Joi.string().required(),
    size: Joi.number().optional(),
    mimetype: Joi.string().optional(),
  })
    .optional()
    .allow(null),
});

// ========== Blockchain ==========
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

// ========== Helpers ==========
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
      else {
        req.write(body);
        req.end();
      }
    } else req.end();
  });
}

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
function coerceJson(val) {
  if (!val) return null;
  if (typeof val === "string") {
    try {
      return JSON.parse(val);
    } catch {
      return null;
    }
  }
  return val;
}
async function extractPdfTextFromDoc(doc) {
  if (!doc?.url) return null;
  const name = doc.name || "";
  const looksPdf = /\.pdf($|\?)/i.test(name) || doc.mimetype === "application/pdf";
  if (!looksPdf) return null;
  const buf = await fetchAsBuffer(doc.url);
  const parsed = await pdfParse(buf);
  const raw = (parsed.text || "").replace(/\s+/g, " ").trim();
  return raw.slice(0, 15000); // cap ~15k chars for prompt size
}

// ========== IPFS ==========
async function pinataUploadFile(file) {
  if (!PINATA_API_KEY || !PINATA_SECRET_API_KEY) throw new Error("Pinata not configured");
  const form = new FormData();
  const buf = Buffer.isBuffer(file.data) ? file.data : Buffer.from(file.data);
  form.append("file", buf, {
    filename: file.name,
    contentType: file.mimetype,
  });
  const { status, body } = await sendRequest(
    "POST",
    "https://api.pinata.cloud/pinning/pinFileToIPFS",
    {
      ...form.getHeaders(),
      pinata_api_key: PINATA_API_KEY,
      pinata_secret_api_key: PINATA_SECRET_API_KEY,
      Accept: "application/json",
    },
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

// ========== Agent2 ==========
async function runAgent2OnBid(bidRow, proposalRow) {
  if (!openai) return null;

  const milestones = Array.isArray(bidRow.milestones)
    ? bidRow.milestones
    : JSON.parse(bidRow.milestones || "[]");

  const docObj = coerceJson(bidRow.doc);
  let pdfText = null;
  try {
    pdfText = await extractPdfTextFromDoc(docObj);
  } catch (e) {
    console.warn("PDF parse failed:", e?.message);
  }

  const prompt = `
You are Agent2. Analyze this vendor bid for a proposal and return strict JSON.

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

${pdfText ? `Bid PDF (excerpt up to ~15k chars):\n${pdfText}\n` : ""}

Return JSON with:
{
  "summary": string,
  "risks": string[],
  "fit": "low" | "medium" | "high",
  "milestoneNotes": string[],
  "confidence": number (0..1)
}
  `.trim();

  try {
    const resp = await openai.chat.completions.create({
      model: "gpt-4o-mini",
      temperature: 0.2,
      messages: [{ role: "user", content: prompt }],
      response_format: { type: "json_object" },
    });

    const raw = resp.choices?.[0]?.message?.content || "{}";
    return JSON.parse(raw);
  } catch (e) {
    console.warn("Agent2 analysis failed:", e?.message);
    return null;
  }
}

// ========== Express ==========
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

// ✅ prevent CDN/browser caching of GETs so polling sees fresh data
app.use((req, res, next) => {
  if (req.method === 'GET') {
    res.set('Cache-Control', 'no-store, no-cache, must-revalidate, max-age=0');
    res.set('Pragma', 'no-cache');
  }
  next();
});

app.use(fileUpload({ limits: { fileSize: 50 * 1024 * 1024 } }));

// ========== Routes ==========

// Health & test
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

// -------- Proposals --------
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
    const { rows } = await pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [
      req.params.id,
    ]);
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
    const { rows } = await pool.query(
      `UPDATE proposals SET status='approved' WHERE proposal_id=$1 RETURNING *`,
      [id]
    );
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
    const { rows } = await pool.query(
      `UPDATE proposals SET status='rejected' WHERE proposal_id=$1 RETURNING *`,
      [id]
    );
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
    const { rows } = await pool.query(
      `UPDATE proposals SET status=$2 WHERE proposal_id=$1 RETURNING *`,
      [id, desired]
    );
    if (!rows[0]) return res.status(404).json({ error: "Proposal not found" });
    res.json(toCamel(rows[0]));
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// -------- Bids --------
app.get("/bids", async (req, res) => {
  try {
    const pid = Number(req.query.proposalId);
    if (Number.isFinite(pid)) {
      const { rows } = await pool.query(
        "SELECT * FROM bids WHERE proposal_id=$1 ORDER BY bid_id DESC",
        [pid]
      );
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
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [id]);
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });
    return res.json(toCamel(rows[0]));
  } catch (err) {
    return res.status(500).json({ error: err.message });
  }
});
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

    // Inline Agent2 analysis (best-effort)
    try {
      const { rows: pr } = await pool.query(
        "SELECT * FROM proposals WHERE proposal_id=$1",
        [inserted.proposal_id]
      );
      const prop = pr[0] || null;
      if (prop) {
        const analysis = await runAgent2OnBid(inserted, prop);
        if (analysis) {
          await pool.query("UPDATE bids SET ai_analysis=$1 WHERE bid_id=$2", [
            JSON.stringify(analysis),
            inserted.bid_id,
          ]);
          inserted.ai_analysis = analysis;
        }
      }
    } catch (e) {
      console.warn("Agent2 post-insert analysis failed:", e?.message);
    }

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
    const { rows } = await pool.query(
      `UPDATE bids SET status='approved' WHERE bid_id=$1 RETURNING *`,
      [id]
    );
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
    const { rows } = await pool.query(
      `UPDATE bids SET status='rejected' WHERE bid_id=$1 RETURNING *`,
      [id]
    );
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
    const { rows } = await pool.query(
      `UPDATE bids SET status=$2 WHERE bid_id=$1 RETURNING *`,
      [id, desired]
    );
    if (!rows[0]) return res.status(404).json({ error: "Bid not found" });
    return res.json(toCamel(rows[0]));
  } catch (err) {
    console.error("patch bid status error", err);
    return res.status(500).json({ error: "Internal error updating bid status" });
  }
});

// Complete/Pay milestone (frontend-compatible)
app.post("/bids/:id/complete-milestone", async (req, res) => {
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

    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [
      JSON.stringify(milestones),
      bidId,
    ]);

    const { rows: updated } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
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
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
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

    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [
      JSON.stringify(milestones),
      bidId,
    ]);

    const { rows: updated } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
    return res.json({ success: true, bid: toCamel(updated[0]), receipt });
  } catch (err) {
    console.error("pay-milestone error", err);
    return res.status(500).json({ error: "Internal error paying milestone" });
  }
});

// Analyze (manual trigger)
app.post("/bids/:id/analyze", async (req, res) => {
  const id = Number(req.params.id);
  if (!Number.isFinite(id)) return res.status(400).json({ error: "Invalid bid id" });
  try {
    const { rows: bids } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [id]);
    if (!bids[0]) return res.status(404).json({ error: "Bid not found" });
    const bid = bids[0];

    const { rows: props } = await pool.query("SELECT * FROM proposals WHERE proposal_id=$1", [
      bid.proposal_id,
    ]);
    const prop = props[0];
    if (!prop) return res.status(404).json({ error: "Proposal not found" });

    const analysis = await runAgent2OnBid(bid, prop);
    if (analysis) {
      await pool.query("UPDATE bids SET ai_analysis=$1 WHERE bid_id=$2", [
        JSON.stringify(analysis),
        id,
      ]);
      const { rows: updated } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [id]);
      return res.json(toCamel(updated[0]));
    }
    return res.status(502).json({ error: "Agent2 failed to produce analysis" });
  } catch (err) {
    console.error("analyze bid error:", err);
    return res.status(500).json({ error: "Agent2 error running analysis" });
  }
});

// (Legacy) keep old complete route for compatibility
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
    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [
      JSON.stringify(milestones),
      bidId,
    ]);
    res.json({ success: true, milestones });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// -------- Proofs --------
app.post("/proofs", async (req, res) => {
  try {
    const { bidId, proofCid, description } = req.body;
    const q =
      "INSERT INTO proofs (bid_id,proof_cid,description,submitted_at,status) VALUES ($1,$2,$3,NOW(),'pending') RETURNING *";
    const { rows } = await pool.query(q, [bidId, proofCid, description]);
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
    const { rows } = await pool.query("SELECT * FROM proofs WHERE bid_id=$1", [
      req.params.bidId,
    ]);
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

// -------- Vendor helpers (simple aliases) --------
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

// -------- Payments (legacy) --------
app.post("/payments/release", async (req, res) => {
  try {
    const { bidId, milestoneIndex } = req.body;
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [bidId]);
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

// -------- IPFS --------
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

// ========== Start ==========
app.listen(PORT, () => {
  console.log(`[api] Listening on :${PORT}`);
});
