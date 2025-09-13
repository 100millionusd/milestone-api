// server.js — Milestone API with USDT/USDC payments + Proofs + Agent2 Postgres mirror
// -----------------------------------------------------------------------------------
require("dotenv").config();
const express = require("express");
const cors = require("cors");
const fileUpload = require("express-fileupload");
const fs = require("fs");
const fsp = fs.promises;
const path = require("path");
const helmet = require("helmet");
const Joi = require("joi");
const { ethers } = require("ethers");
const FormData = require("form-data");
const https = require("https");
const http = require("http");

// NEW: optional Postgres (for Agent 2)
let Pool = null;
try {
  ({ Pool } = require("pg"));
} catch (_) {
  // pg not installed; mirroring to Agent2 DB will be disabled automatically
}

// ========== Config ==========
const PORT = Number(process.env.PORT || 3000);

// Allow one or many origins (comma-separated) — default to your Netlify site
const DEFAULT_ORIGIN = "https://lithiumx.netlify.app";
const CORS_ORIGINS = (process.env.CORS_ORIGINS || process.env.CORS_ORIGIN || DEFAULT_ORIGIN)
  .split(",")
  .map((s) => s.trim())
  .filter(Boolean);

// Pinata via API key + secret (NO JWT)
const PINATA_API_KEY = (process.env.PINATA_API_KEY || "").trim();
const PINATA_SECRET_API_KEY = (process.env.PINATA_SECRET_API_KEY || "").trim();
const PINATA_GATEWAY = process.env.PINATA_GATEWAY_DOMAIN || "gateway.pinata.cloud";

// Blockchain configuration
const NETWORK = process.env.NETWORK || "sepolia";
const SEPOLIA_RPC_URL = process.env.SEPOLIA_RPC_URL || "https://ethereum-sepolia.publicnode.com";
const PRIVATE_KEY = process.env.PRIVATE_KEY || "";
const ESCROW_ADDR = process.env.ESCROW_ADDR || "";

// Sepolia token addresses
const USDC_ADDRESS = process.env.USDC_ADDRESS || "0x1c7D4B196Cb0C7B01d743Fbc6116a902379C7238";
const USDT_ADDRESS = process.env.USDT_ADDRESS || "0x7169D38820dfd117C3FA1f22a697dBA58d90BA06";

// ERC20 ABI (simplified)
const ERC20_ABI = [
  "function transfer(address to, uint256 amount) returns (bool)",
  "function balanceOf(address account) view returns (uint256)",
  "function decimals() view returns (uint8)",
  "function approve(address spender, uint256 amount) returns (bool)",
];

// Token configurations
const TOKENS = {
  USDC: { address: USDC_ADDRESS, decimals: 6 },
  USDT: { address: USDT_ADDRESS, decimals: 6 },
};

// NEW: Agent 2 DB (same Postgres your worker uses)
const AGENT2_DATABASE_URL = process.env.AGENT2_DATABASE_URL || process.env.DATABASE_URL || "";
const agentPool =
  Pool && AGENT2_DATABASE_URL
    ? new Pool({ connectionString: AGENT2_DATABASE_URL, ssl: { rejectUnauthorized: false } })
    : null;

// NEW: exchange rate for BOB (used by Agent 2 table's NOT NULL price_bol)
const BOB_RATE = Number(process.env.BOB_RATE || 6.9);

// ========== Validation Schemas ==========
const proposalSchema = Joi.object({
  orgName: Joi.string().min(1).max(100).required(),
  title: Joi.string().min(1).max(200).required(),
  summary: Joi.string().min(1).max(1000).required(),
  contact: Joi.string().email().required(),
  address: Joi.string().max(200).optional().allow(""),
  city: Joi.string().max(100).optional().allow(""),
  country: Joi.string().max(100).optional().allow(""),
  amountUSD: Joi.number().min(0).optional().default(0),
  docs: Joi.array().optional().default([]),
  cid: Joi.string().optional().allow(""),
});

const bidSchema = Joi.object({
  proposalId: Joi.number().integer().min(1).required(),
  vendorName: Joi.string().min(1).max(100).required(),
  priceUSD: Joi.number().min(0).required(),
  days: Joi.number().integer().min(0).required(),
  notes: Joi.string().max(1000).optional().allow(""),
  walletAddress: Joi.string()
    .pattern(/^0x[a-fA-F0-9]{40}$/)
    .required()
    .messages({
      "string.pattern.base": "Wallet address must be a valid Ethereum address",
    }),
  preferredStablecoin: Joi.string().valid("USDT", "USDC").default("USDT"),
  milestones: Joi.array()
    .items(
      Joi.object({
        name: Joi.string().required(),
        amount: Joi.number().min(0).required(),
        dueDate: Joi.date().iso().required(),
      })
    )
    .min(1)
    .required(),
  doc: Joi.object({
    cid: Joi.string().required(),
    url: Joi.string().uri().required(),
    name: Joi.string().required(),
    size: Joi.number().required(),
  })
    .optional()
    .allow(null),

  aiAnalysis: Joi.any().optional(),
});

// JSON schema for Pinata upload-json
const pinataJsonSchema = Joi.object({
  title: Joi.string().max(200).required(),
  description: Joi.string().max(2000).optional().allow(""),
  files: Joi.array()
    .items(
      Joi.object({
        cid: Joi.string().required(),
        name: Joi.string().required(),
        url: Joi.string().uri().required(),
      })
    )
    .optional()
    .default([]),
});

// ========== Database Layer (JSON files) ==========
class JSONDatabase {
  constructor(filePath) {
    this.filePath = filePath;
  }
  async read() {
    try {
      const data = await fsp.readFile(this.filePath, "utf8");
      return JSON.parse(data || "[]");
    } catch (error) {
      if (error.code === "ENOENT") {
        await this.write([]);
        return [];
      }
      throw error;
    }
  }
  async write(data) {
    await fsp.mkdir(path.dirname(this.filePath), { recursive: true });
    await fsp.writeFile(this.filePath, JSON.stringify(data, null, 2));
  }
  async findById(id) {
    const data = await this.read();
    return data.find((item) => item.proposalId === id || item.bidId === id);
  }
  async findByProposalId(proposalId) {
    const data = await this.read();
    return data.filter((item) => item.proposalId === proposalId);
  }
  async add(item) {
    const data = await this.read();
    data.push(item);
    await this.write(data);
    return item;
  }
  async update(id, updates) {
    const data = await this.read();
    const idx = data.findIndex((item) => item.proposalId === id || item.bidId === id);
    if (idx === -1) return null;
    data[idx] = { ...data[idx], ...updates };
    await this.write(data);
    return data[idx];
  }
}

// ========== Blockchain Service ==========
class BlockchainService {
  constructor() {
    this.provider = new ethers.JsonRpcProvider(SEPOLIA_RPC_URL);
    if (PRIVATE_KEY) {
      const pk = PRIVATE_KEY.startsWith("0x") ? PRIVATE_KEY : `0x${PRIVATE_KEY}`;
      this.signer = new ethers.Wallet(pk, this.provider);
      console.log(`Blockchain service initialized with address: ${this.signer.address}`);
    } else {
      console.warn("No private key provided. Blockchain functions will be disabled.");
      this.signer = null;
    }
  }
  async sendToken(tokenSymbol, toAddress, amount) {
    if (!this.signer) throw new Error("Blockchain service not configured. Provide PRIVATE_KEY.");
    const token = TOKENS[tokenSymbol];
    if (!token) throw new Error(`Unsupported token: ${tokenSymbol}`);
    if (!ethers.isAddress(toAddress)) throw new Error("Invalid recipient address");

    const contract = new ethers.Contract(token.address, ERC20_ABI, this.signer);
    const decimals = await contract.decimals();
    const amountInWei = ethers.parseUnits(amount.toString(), decimals);

    const balance = await contract.balanceOf(await this.signer.getAddress());
    if (balance < amountInWei) throw new Error("Insufficient balance for payment");

    const tx = await contract.transfer(toAddress, amountInWei);
    const receipt = await tx.wait();
    if (!receipt.status) throw new Error("Transaction failed");

    return {
      success: true,
      transactionHash: receipt.hash,
      amount,
      toAddress,
      currency: tokenSymbol,
    };
  }
  async getBalance(tokenSymbol) {
    if (!this.signer) return 0;
    const token = TOKENS[tokenSymbol];
    if (!token) throw new Error(`Unsupported token: ${tokenSymbol}`);
    const contract = new ethers.Contract(token.address, ERC20_ABI, this.signer);
    const balance = await contract.balanceOf(await this.signer.getAddress());
    const decimals = await contract.decimals();
    return parseFloat(ethers.formatUnits(balance, decimals));
  }
  async getTransactionStatus(txHash) {
    const receipt = await this.provider.getTransactionReceipt(txHash);
    if (!receipt) return { status: "not_found" };
    return {
      status: receipt.status === 1 ? "success" : "failed",
      blockNumber: receipt.blockNumber,
      confirmations: receipt.confirmations,
    };
  }
  isConfigured() {
    return this.signer !== null;
  }
}

// ========== App ==========
const app = express();
const blockchainService = new BlockchainService();

// Add trust proxy for Railway
app.set("trust proxy", 1);

// ===== CORS =====
app.use((req, res, next) => {
  const origin = req.headers.origin;
  const allowed = !origin || CORS_ORIGINS.includes(origin);
  if (allowed && origin) {
    res.header("Access-Control-Allow-Origin", origin);
    res.header("Vary", "Origin");
  }
  res.header("Access-Control-Allow-Credentials", "true");
  res.header("Access-Control-Allow-Headers", "Content-Type, Authorization, X-Requested-With");
  res.header("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE, OPTIONS, PATCH");
  if (req.method === "OPTIONS") return res.sendStatus(204);
  next();
});
app.use(
  cors({
    origin: (origin, cb) => {
      if (!origin) return cb(null, true);
      return CORS_ORIGINS.includes(origin) ? cb(null, true) : cb(new Error("Not allowed by CORS"));
    },
    credentials: true,
  })
);

// Security
app.use(helmet());

// Body / files
app.use(express.json({ limit: "20mb" }));
app.use(
  fileUpload({
    limits: { fileSize: 50 * 1024 * 1024 }, // 50MB
    useTempFiles: false,
    abortOnLimit: true,
  })
);

// ========== Initialize JSON DB ==========
const DATA_DIR = path.join(__dirname, "data");
const PROPOSALS_FILE = path.join(DATA_DIR, "proposals.json");
const BIDS_FILE = path.join(DATA_DIR, "bids.json");

const proposalsDB = new JSONDatabase(PROPOSALS_FILE);
const bidsDB = new JSONDatabase(BIDS_FILE);

function toNumber(v, d = 0) {
  const n = Number(v);
  return Number.isFinite(n) ? n : d;
}

// ========== Minimal HTTP helpers (no node-fetch needed) ==========
function sendRequest(method, urlStr, headers = {}, bodyStreamOrString = null) {
  const u = new URL(urlStr);
  const lib = u.protocol === "https:" ? https : http;
  const options = { method, hostname: u.hostname, port: u.port || (u.protocol === "https:" ? 443 : 80), path: u.pathname + u.search, headers };
  return new Promise((resolve, reject) => {
    const req = lib.request(options, (res) => {
      let data = "";
      res.setEncoding("utf8");
      res.on("data", (c) => (data += c));
      res.on("end", () => resolve({ status: res.statusCode || 0, body: data }));
    });
    req.on("error", reject);
    if (bodyStreamOrString && typeof bodyStreamOrString.pipe === "function") {
      bodyStreamOrString.pipe(req);
    } else if (bodyStreamOrString) {
      req.write(bodyStreamOrString);
      req.end();
    } else {
      req.end();
    }
  });
}

// ========== IPFS / Pinata (API key + secret) ==========
// ... (UNCHANGED: pinataUploadFile, pinataUploadJson)
async function pinataUploadFile(oneFile) {
  if (!PINATA_API_KEY || !PINATA_SECRET_API_KEY) {
    throw new Error("No Pinata auth configured (PINATA_API_KEY/SECRET).");
  }
  const form = new FormData();
  const buf =
    oneFile && oneFile.data
      ? Buffer.isBuffer(oneFile.data)
        ? oneFile.data
        : Buffer.from(oneFile.data)
      : Buffer.from([]);
  form.append("file", buf, {
    filename: oneFile?.name || "upload.bin",
    contentType: oneFile?.mimetype || "application/octet-stream",
  });
  const headers = {
    ...form.getHeaders(),
    pinata_api_key: PINATA_API_KEY,
    pinata_secret_api_key: PINATA_SECRET_API_KEY,
    Accept: "application/json",
  };
  const { status, body } = await sendRequest(
    "POST",
    "https://api.pinata.cloud/pinning/pinFileToIPFS",
    headers,
    form
  );
  let json;
  try {
    json = body ? JSON.parse(body) : {};
  } catch {
    throw new Error(`Pinata pinFileToIPFS bad JSON: ${body}`);
  }
  if (status < 200 || status >= 300) {
    throw new Error(json?.error?.details || json?.error || json?.message || `Pinata error (${status})`);
  }
  const cid = json.IpfsHash || json.cid || json?.pin?.cid;
  if (!cid) throw new Error("Pinata response missing CID");
  const url = `https://${PINATA_GATEWAY}/ipfs/${cid}`;
  return { cid, url, size: oneFile?.size || 0, name: oneFile?.name || "file" };
}
async function pinataUploadJson(obj) {
  if (!PINATA_API_KEY || !PINATA_SECRET_API_KEY) {
    throw new Error("No Pinata auth configured (PINATA_API_KEY/SECRET).");
  }
  const payload = JSON.stringify(obj || {});
  const headers = {
    "content-type": "application/json",
    "content-length": Buffer.byteLength(payload),
    pinata_api_key: PINATA_API_KEY,
    pinata_secret_api_key: PINATA_SECRET_API_KEY,
    Accept: "application/json",
  };
  const { status, body } = await sendRequest(
    "POST",
    "https://api.pinata.cloud/pinning/pinJSONToIPFS",
    headers,
    payload
  );
  let json;
  try {
    json = body ? JSON.parse(body) : {};
  } catch {
    throw new Error(`Pinata pinJSONToIPFS bad JSON: ${body}`);
  }
  if (status < 200 || status >= 300) {
    throw new Error(json?.error?.details || json?.error || json?.message || `Pinata error (${status})`);
  }
  const cid = json.IpfsHash || json.cid || json?.pin?.cid;
  if (!cid) throw new Error("Pinata response missing CID");
  const url = `https://${PINATA_GATEWAY}/ipfs/${cid}`;
  return { cid, url };
}

// ========== Routes ==========

// Health
app.get("/health", async (_req, res) => {
  try {
    const proposals = await proposalsDB.read();
    const bids = await bidsDB.read();

    let blockchainStatus = "not_configured";
    let signerAddress = null;
    let balances = {};

    if (blockchainService.isConfigured()) {
      blockchainStatus = "configured";
      signerAddress = await blockchainService.signer.getAddress();
      try {
        balances.USDC = await blockchainService.getBalance("USDC");
        balances.USDT = await blockchainService.getBalance("USDT");
      } catch (error) {
        console.error("Error fetching balances:", error);
        balances.error = error.message;
      }
    }

    res.json({
      ok: true,
      network: NETWORK,
      rpc: SEPOLIA_RPC_URL ? "(set)" : "",
      escrow: ESCROW_ADDR || "",
      signer: signerAddress,
      blockchain: blockchainStatus,
      balances,
      pinata: !!(PINATA_API_KEY && PINATA_SECRET_API_KEY),
      agent2: { db: !!agentPool, bobRate: BOB_RATE },
      counts: { proposals: proposals.length, bids: bids.length },
    });
  } catch (error) {
    res.status(500).json({ error: "Health check failed" });
  }
});

// Test endpoint
app.get("/test", async (_req, res) => {
  try {
    const bids = await bidsDB.read();
    let blockchainInfo = { configured: blockchainService.isConfigured() };
    if (blockchainService.isConfigured()) {
      blockchainInfo.signerAddress = await blockchainService.signer.getAddress();
    }
    res.json({
      success: true,
      bidCount: bids.length,
      sampleBid: bids[0] || null,
      blockchain: blockchainInfo,
      agent2Db: !!agentPool,
      message: "Server is working correctly",
    });
  } catch (error) {
    res.status(500).json({ error: "Test failed", message: error.message });
  }
});

// Balances & transactions (UNCHANGED)
app.get("/balances/:address", async (req, res) => {
  try {
    const { address } = req.params;
    if (!ethers.isAddress(address)) return res.status(400).json({ error: "Invalid address" });
    const balances = {};
    for (const [symbol, token] of Object.entries(TOKENS)) {
      try {
        const contract = new ethers.Contract(token.address, ERC20_ABI, blockchainService.provider);
        const balance = await contract.balanceOf(address);
        balances[symbol] = ethers.formatUnits(balance, token.decimals);
      } catch (error) {
        console.error(`Error fetching ${symbol} balance:`, error);
        balances[symbol] = "0";
      }
    }
    res.json(balances);
  } catch (error) {
    console.error("Error in balances endpoint:", error);
    res.status(500).json({ error: "Internal server error" });
  }
});
app.get("/transaction/:txHash", async (req, res) => {
  try {
    const { txHash } = req.params;
    const status = await blockchainService.getTransactionStatus(txHash);
    res.json(status);
  } catch (error) {
    console.error("Error fetching transaction:", error);
    res.status(500).json({ error: "Failed to fetch transaction" });
  }
});

// Uploads (files)
app.post("/ipfs/upload-file", async (req, res) => {
  try {
    const f = req.files?.file || req.files?.files;
    if (!f) return res.status(400).json({ error: "file is required" });
    const files = Array.isArray(f) ? f : [f];
    const results = [];
    for (const one of files) {
      try {
        const uploaded = await pinataUploadFile(one);
        results.push(uploaded);
      } catch (err) {
        console.error("Pinata upload failed for file:", one?.name, err);
        return res.status(400).json({ error: "Pinata upload failed", details: err?.message || String(err) });
      }
    }
    if (Array.isArray(f)) res.json({ files: results });
    else res.json(results[0]);
  } catch (e) {
    console.error("/ipfs/upload-file error:", e);
    res.status(400).json({ error: String(e.message || e) });
  }
});
app.post("/ipfs/upload-json", async (req, res) => {
  try {
    const { error, value } = pinataJsonSchema.validate(req.body, { abortEarly: true });
    if (error) return res.status(400).json({ error: error.details[0].message });
    const info = await pinataUploadJson(value);
    res.json(info);
  } catch (e) {
    console.error("/ipfs/upload-json error:", e);
    res.status(400).json({ error: String(e.message || e) });
  }
});

// Proposals
app.post("/proposals", async (req, res) => {
  try {
    const { error, value } = proposalSchema.validate(req.body);
    if (error) return res.status(400).json({ error: error.details[0].message });

    const proposals = await proposalsDB.read();
    const proposalId = proposals.length ? proposals[proposals.length - 1].proposalId + 1 : 1;

    const record = {
      proposalId,
      orgName: value.orgName,
      title: value.title,
      summary: value.summary,
      contact: value.contact,
      address: value.address || "",
      city: value.city || "",
      country: value.country || "",
      amountUSD: value.amountUSD,
      docs: value.docs || [],
      cid: value.cid || "",
      status: "pending",
      createdAt: new Date().toISOString(),
    };

    await proposalsDB.add(record);
    res.json({ ok: true, proposalId, cid: record.cid || null });
  } catch (error) {
    console.error("Error creating proposal:", error);
    res.status(500).json({ error: "Failed to create proposal" });
  }
});
app.get("/proposals", async (_req, res) => {
  try {
    const proposals = await proposalsDB.read();
    res.json(proposals);
  } catch (error) {
    console.error("Error fetching proposals:", error);
    res.status(500).json({ error: "Failed to fetch proposals" });
  }
});
app.get("/proposals/:id", async (req, res) => {
  try {
    const id = toNumber(req.params.id, -1);
    const proposal = await proposalsDB.findById(id);
    if (!proposal) return res.status(404).json({ error: "proposal 404" });
    res.json(proposal);
  } catch (error) {
    console.error("Error fetching proposal:", error);
    res.status(500).json({ error: "Failed to fetch proposal" });
  }
});
app.post("/proposals/:id/approve", async (req, res) => {
  try {
    const id = toNumber(req.params.id, -1);
    const updated = await proposalsDB.update(id, { status: "approved" });
    if (!updated) return res.status(404).json({ error: "proposal 404" });
    res.json({ ok: true, proposalId: id, status: "approved" });
  } catch (error) {
    console.error("Error approving proposal:", error);
    res.status(500).json({ error: "Failed to approve proposal" });
  }
});
app.post("/proposals/:id/reject", async (req, res) => {
  try {
    const id = toNumber(req.params.id, -1);
    const updated = await proposalsDB.update(id, { status: "rejected" });
    if (!updated) return res.status(404).json({ error: "proposal 404" });
    res.json({ ok: true, proposalId: id, status: "rejected" });
  } catch (error) {
    console.error("Error rejecting proposal:", error);
    res.status(500).json({ error: "Failed to reject proposal" });
  }
});

// Bids
app.post("/bids", async (req, res) => {
  try {
    const { error, value } = bidSchema.validate(req.body);
    if (error) return res.status(400).json({ error: error.details[0].message });

    const proposal = await proposalsDB.findById(value.proposalId);
    if (!proposal) return res.status(404).json({ error: "proposal 404" });

    const bids = await bidsDB.read();
    const bidId = bids.length ? bids[bids.length - 1].bidId + 1 : 1;

    const rec = {
      bidId,
      proposalId: value.proposalId,
      vendorName: value.vendorName,
      priceUSD: value.priceUSD,
      days: value.days,
      notes: value.notes || "",
      walletAddress: value.walletAddress,
      preferredStablecoin: value.preferredStablecoin,
      milestones: value.milestones.map((m) => ({
        ...m,
        completed: false,
        completionDate: null,
        proof: "",
        approved: null,
        paymentTxHash: null,
        paymentDate: null,
      })),
      doc: value.doc || null,
      aiAnalysis: value.aiAnalysis || null,
      status: "pending",
      createdAt: new Date().toISOString(),
    };

    await bidsDB.add(rec);

    // Respond immediately (frontend shows "⏳ Analysis pending..." until merged)
    res.json({
      ok: true,
      bidId,
      proposalId: value.proposalId,
      aiAnalysis: rec.aiAnalysis || null,
    });

    // === Agent 2: mirror to Postgres for worker ===
    // (fire-and-forget, doesn't block the response)
    (async () => {
      if (!agentPool) return;

      const price_bol = Number((rec.priceUSD * BOB_RATE).toFixed(2));
      const milestonesJson = JSON.stringify(rec.milestones);
      const docJson = rec.doc ? JSON.stringify(rec.doc) : null;

      // Insert into vendor-agent Postgres; worker will analyze and fill ai_analysis
      const insertSql = `
        INSERT INTO bids
          (proposal_id, vendor_name, price_usd, price_bol, days, notes, wallet_address,
           preferred_stablecoin, milestones, doc, ai_analysis, status, created_at)
        VALUES
          ($1,$2,$3,$4,$5,$6,$7,$8,$9::jsonb,$10::jsonb,$11::jsonb,$12, NOW())
        RETURNING bid_id
      `;
      const params = [
        rec.proposalId,
        rec.vendorName,
        rec.priceUSD,
        price_bol,
        rec.days,
        rec.notes,
        rec.walletAddress,
        rec.preferredStablecoin,
        milestonesJson,
        docJson,
        null,
        rec.status,
      ];

      try {
        const { rows } = await agentPool.query(insertSql, params);
        const pgBidId = rows?.[0]?.bid_id;
        if (pgBidId) {
          // save mapping so we can merge ai_analysis later in GET
          await bidsDB.update(rec.bidId, { pgBidId });
          console.log(`[agent2] mirrored bid ${rec.bidId} -> pgBidId ${pgBidId}`);
        }
      } catch (e) {
        console.error("[agent2] mirror failed:", e.message);
      }
    })();
  } catch (error) {
    console.error("Error creating bid:", error);
    res.status(500).json({ error: "Failed to create bid" });
  }
});

app.get("/bids", async (req, res) => {
  try {
    const pid = toNumber(req.query.proposalId, 0);
    const bids = await bidsDB.read();

    let filteredBids = bids;
    if (pid) {
      filteredBids = bids.filter((b) => b.proposalId === pid);
      if (filteredBids.length === 0) {
        const proposals = await proposalsDB.read();
        const proposalExists = proposals.some((p) => p.proposalId === pid);
        if (!proposalExists) {
          return res.status(404).json({ error: "Proposal not found", proposalId: pid });
        }
      }
    }

    // === Merge Agent 2 analysis from Postgres, if we have mappings ===
    if (agentPool) {
      const mappedIds = filteredBids.filter((b) => b.pgBidId).map((b) => b.pgBidId);
      if (mappedIds.length) {
        try {
          const { rows } = await agentPool.query(
            `SELECT bid_id, ai_analysis FROM bids WHERE bid_id = ANY($1::int[])`,
            [mappedIds]
          );
          const map = new Map(rows.map((r) => [r.bid_id, r.ai_analysis]));
          filteredBids = filteredBids.map((b) => {
            if (b.pgBidId && map.has(b.pgBidId) && map.get(b.pgBidId)) {
              return { ...b, aiAnalysis: map.get(b.pgBidId) };
            }
            return b;
          });
        } catch (e) {
          console.warn("[agent2] merge skipped:", e.message);
        }
      }
    }

    res.json(filteredBids);
  } catch (error) {
    console.error("Error fetching bids:", error);
    res.status(500).json({
      error: "Failed to fetch bids",
      details: process.env.NODE_ENV === "development" ? error.message : undefined,
    });
  }
});

app.get("/bids/:id", async (req, res) => {
  try {
    const id = toNumber(req.params.id, -1);
    let bid = await bidsDB.findById(id);
    if (!bid) return res.status(404).json({ error: "bid 404" });

    // Merge Agent 2 analysis for this one bid
    if (agentPool && bid.pgBidId) {
      try {
        const { rows } = await agentPool.query(
          `SELECT ai_analysis FROM bids WHERE bid_id = $1`,
          [bid.pgBidId]
        );
        const ai = rows?.[0]?.ai_analysis;
        if (ai) bid = { ...bid, aiAnalysis: ai };
      } catch (e) {
        console.warn("[agent2] single merge skipped:", e.message);
      }
    }

    res.json(bid);
  } catch (error) {
    console.error("Error fetching bid:", error);
    res.status(500).json({ error: "Failed to fetch bid" });
  }
});

app.post("/bids/:id/approve", async (req, res) => {
  try {
    const id = toNumber(req.params.id, -1);
    const bids = await bidsDB.read();
    const i = bids.findIndex((b) => b.bidId === id);
    if (i < 0) return res.status(404).json({ error: "bid 404" });
    bids[i].status = "approved";
    await bidsDB.write(bids);
    res.json({ ok: true, bidId: id, status: "approved" });
  } catch (error) {
    console.error("Error approving bid:", error);
    res.status(500).json({ error: "Failed to approve bid" });
  }
});

app.post("/bids/:id/reject", async (req, res) => {
  try {
    const id = toNumber(req.params.id, -1);
    const bids = await bidsDB.read();
    const i = bids.findIndex((b) => b.bidId === id);
    if (i < 0) return res.status(404).json({ error: "bid 404" });
    bids[i].status = "rejected";
    await bidsDB.write(bids);
    res.json({ ok: true, bidId: id, status: "rejected" });
  } catch (error) {
    console.error("Error rejecting bid:", error);
    res.status(500).json({ error: "Failed to reject bid" });
  }
});

app.post("/bids/:id/complete-milestone", async (req, res) => {
  try {
    const id = toNumber(req.params.id, -1);
    const { milestoneIndex, proof } = req.body;
    const bids = await bidsDB.read();
    const i = bids.findIndex((b) => b.bidId === id);
    if (i < 0) return res.status(404).json({ error: "bid 404" });
    if (!bids[i].milestones[milestoneIndex]) {
      return res.status(400).json({ error: "milestone not found" });
    }
    bids[i].milestones[milestoneIndex].completed = true;
    bids[i].milestones[milestoneIndex].completionDate = new Date().toISOString();
    bids[i].milestones[milestoneIndex].proof = proof || "";
    const allCompleted = bids[i].milestones.every((m) => m.completed);
    if (allCompleted) bids[i].status = "completed";
    await bidsDB.write(bids);
    res.json({ ok: true, bidId: id, milestoneIndex });
  } catch (error) {
    console.error("Error completing milestone:", error);
    res.status(500).json({ error: "Failed to complete milestone" });
  }
});

// Pay milestone with real USDT/USDC
app.post("/bids/:id/pay-milestone", async (req, res) => {
  try {
    const id = toNumber(req.params.id, -1);
    const { milestoneIndex } = req.body;
    const bids = await bidsDB.read();
    const i = bids.findIndex((b) => b.bidId === id);
    if (i < 0) return res.status(404).json({ error: "bid 404" });

    const bid = bids[i];
    const milestone = bid.milestones[milestoneIndex];
    if (!milestone) return res.status(400).json({ error: "milestone not found" });
    if (!milestone.completed) return res.status(400).json({ error: "milestone not completed" });
    if (milestone.paymentTxHash) return res.status(400).json({ error: "milestone already paid" });

    const paymentResult = await blockchainService.sendToken(
      bid.preferredStablecoin,
      bid.walletAddress,
      milestone.amount
    );
    milestone.paymentTxHash = paymentResult.transactionHash;
    milestone.paymentDate = new Date().toISOString();
    await bidsDB.write(bids);

    res.json({
      ok: true,
      bidId: id,
      milestoneIndex,
      transactionHash: paymentResult.transactionHash,
    });
  } catch (error) {
    console.error("Error paying milestone:", error);
    res.status(500).json({
      error: error.message || "Failed to pay milestone",
      details: process.env.NODE_ENV === "development" ? error.stack : undefined,
    });
  }
});

// ======== PROOFS (UNCHANGED) ========
function parseProof(proofStr) {
  if (!proofStr) return {};
  try {
    const j = JSON.parse(proofStr);
    return typeof j === "object" && j ? j : {};
  } catch {
    return { raw: proofStr };
  }
}
app.get("/proofs", async (_req, res) => {
  try {
    const bids = await bidsDB.read();
    const out = [];
    for (const bid of bids) {
      bid.milestones.forEach((m, idx) => {
        if (m.proof) {
          const p = parseProof(m.proof);
          out.push({
            bidId: bid.bidId,
            proposalId: bid.proposalId,
            vendorName: bid.vendorName,
            walletAddress: bid.walletAddress,
            milestoneIndex: idx,
            milestoneName: m.name,
            amount: m.amount,
            dueDate: m.dueDate,
            title: p.title || `Milestone: ${m.name}`,
            description: p.description || "",
            files: Array.isArray(p.files) ? p.files : [],
            status:
              m.approved === true ? "approved" : m.approved === false ? "rejected" : "pending",
            submittedAt: m.completionDate || bid.createdAt,
          });
        }
      });
    }
    res.json(out);
  } catch (err) {
    console.error("Error fetching proofs:", err);
    res.status(500).json({ error: "Failed to fetch proofs" });
  }
});
app.post("/proofs/:bidId/:milestoneIndex/approve", async (req, res) => {
  try {
    const bidId = toNumber(req.params.bidId, -1);
    const milestoneIndex = toNumber(req.params.milestoneIndex, -1);
    const bids = await bidsDB.read();
    const i = bids.findIndex((b) => b.bidId === bidId);
    if (i < 0) return res.status(404).json({ error: "bid not found" });
    const m = bids[i].milestones[milestoneIndex];
    if (!m) return res.status(400).json({ error: "milestone not found" });
    if (!m.proof) return res.status(400).json({ error: "no proof submitted" });
    m.approved = true;
    await bidsDB.write(bids);
    res.json({ ok: true, bidId, milestoneIndex, approved: true });
  } catch (err) {
    console.error("Error approving proof:", err);
    res.status(500).json({ error: "Failed to approve proof" });
  }
});
app.post("/proofs/:bidId/:milestoneIndex/reject", async (req, res) => {
  try {
    const bidId = toNumber(req.params.bidId, -1);
    const milestoneIndex = toNumber(req.params.milestoneIndex, -1);
    const bids = await bidsDB.read();
    const i = bids.findIndex((b) => b.bidId === bidId);
    if (i < 0) return res.status(404).json({ error: "bid not found" });
    const m = bids[i].milestones[milestoneIndex];
    if (!m) return res.status(400).json({ error: "milestone not found" });
    if (!m.proof) return res.status(400).json({ error: "no proof submitted" });
    m.approved = false;
    await bidsDB.write(bids);
    res.json({ ok: true, bidId, milestoneIndex, approved: false });
  } catch (err) {
    console.error("Error rejecting proof:", err);
    res.status(500).json({ error: "Failed to reject proof" });
  }
});

// Centralized error handling
app.use((error, _req, res, _next) => {
  console.error("Unhandled error:", error);
  res.status(500).json({
    error: process.env.NODE_ENV === "production" ? "Internal server error" : error.message,
  });
});

// Helpful JSON 404 for API-ish paths
app.use((req, res, next) => {
  if (
    req.path.startsWith("/api") ||
    req.path.match(/^\/(proposals|bids|ipfs|health|test|balances|transaction|proofs|vendor)/)
  ) {
    return res.status(404).json({ error: "route 404" });
  }
  next();
});

// ========== Environment Validation ==========
function validateEnv() {
  if (!PINATA_API_KEY || !PINATA_SECRET_API_KEY) {
    console.warn("Warning: PINATA_API_KEY / PINATA_SECRET_API_KEY not set — Pinata uploads will fail.");
  }
  if (!agentPool) {
    console.warn("Agent2 DB mirroring disabled (no AGENT2_DATABASE_URL or 'pg' not installed).");
  }
}

// ========== Start ==========
validateEnv();

async function startServer() {
  try {
    await proposalsDB.read();
    await bidsDB.read();

    app.listen(PORT, () => {
      console.log(`[api] listening on :${PORT}`);
      console.log(`[api] Allowed CORS origins: ${CORS_ORIGINS.join(", ")}`);
      console.log(`[api] Pinata configured: ${!!(PINATA_API_KEY && PINATA_SECRET_API_KEY)}`);
      console.log(`[api] Blockchain configured: ${blockchainService.isConfigured()}`);
      if (blockchainService.isConfigured()) {
        console.log(`[api] Signer address: ${blockchainService.signer.address}`);
      }
      console.log(`[api] Agent2 DB: ${!!agentPool}`);
      console.log(`[api] Test endpoint: http://localhost:${PORT}/test`);
      console.log(`[api] Health endpoint: http://localhost:${PORT}/health`);
    });
  } catch (error) {
    console.error("Failed to start server:", error);
    process.exit(1);
  }
}

startServer();
