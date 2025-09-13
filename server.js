// server.js — Milestone API (Postgres + Blockchain + IPFS/Pinata)
// ------------------------------------------------------------------
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

// Blockchain
const NETWORK = process.env.NETWORK || "sepolia";
const SEPOLIA_RPC_URL =
  process.env.SEPOLIA_RPC_URL || "https://ethereum-sepolia.publicnode.com";
const PRIVATE_KEY = process.env.PRIVATE_KEY || "";
const USDC_ADDRESS =
  process.env.USDC_ADDRESS ||
  "0x1c7D4B196Cb0C7B01d743Fbc6116a902379C7238";
const USDT_ADDRESS =
  process.env.USDT_ADDRESS ||
  "0x7169D38820dfd117C3FA1f22a697dBA58d90BA06";

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

const bidSchema = Joi.object({
  proposalId: Joi.number().integer().required(),
  vendorName: Joi.string().required(),
  priceUSD: Joi.number().required(),
  priceBol: Joi.number().required(),
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
    cid: Joi.string().required(),
    url: Joi.string().uri().required(),
    name: Joi.string().required(),
    size: Joi.number().required(),
  })
    .optional()
    .allow(null),
});

// ========== Blockchain Service ==========
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
      res.on("end", () =>
        resolve({ status: res.statusCode || 0, body: data })
      );
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

// ========== IPFS/Pinata ==========
async function pinataUploadFile(file) {
  if (!PINATA_API_KEY || !PINATA_SECRET_API_KEY)
    throw new Error("Pinata not configured");
  const form = new FormData();
  const buf = Buffer.isBuffer(file.data)
    ? file.data
    : Buffer.from(file.data);
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
  const json = JSON.parse(body);
  if (status < 200 || status >= 300) throw new Error(json?.error || "Pinata error");
  const cid = json.IpfsHash;
  return {
    cid,
    url: `https://${PINATA_GATEWAY}/ipfs/${cid}`,
    size: file.size,
    name: file.name,
  };
}

// ========== Express ==========
const app = express();

// Trust Railway proxy
app.set("trust proxy", 1);

// CORS middleware
app.use(
  cors({
    origin: function (origin, callback) {
      if (!origin) return callback(null, true);
      if (CORS_ORIGINS.includes(origin)) return callback(null, true);
      return callback(new Error("Not allowed by CORS: " + origin));
    },
    credentials: true,
  })
);

app.use(helmet());
app.use(express.json({ limit: "20mb" }));
app.use(fileUpload({ limits: { fileSize: 50 * 1024 * 1024 } }));

// ========== Routes ==========

// Health
app.get("/health", async (_req, res) => {
  try {
    const { rows: proposals } = await pool.query(
      "SELECT COUNT(*) FROM proposals"
    );
    const { rows: bids } = await pool.query("SELECT COUNT(*) FROM bids");
    res.json({
      ok: true,
      proposals: proposals[0].count,
      bids: bids[0].count,
      blockchain: blockchainService.signer ? "configured" : "not_configured",
    });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// ---------- Proposals ----------
app.post("/proposals", async (req, res) => {
  try {
    const { error, value } = proposalSchema.validate(req.body);
    if (error) return res.status(400).json({ error: error.message });
    const q = `INSERT INTO proposals (org_name,title,summary,contact,address,city,country,amount_usd,docs,cid)
               VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10) RETURNING *`;
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
    res.json(rows[0]);
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get("/proposals", async (_req, res) => {
  const { rows } = await pool.query("SELECT * FROM proposals ORDER BY created_at DESC");
  res.json(rows);
});

app.get("/proposals/:id", async (req, res) => {
  const { rows } = await pool.query(
    "SELECT * FROM proposals WHERE proposal_id=$1",
    [req.params.id]
  );
  if (!rows[0]) return res.status(404).json({ error: "proposal not found" });
  res.json(rows[0]);
});

// ---------- Bids ----------
app.post("/bids", async (req, res) => {
  try {
    const { error, value } = bidSchema.validate(req.body);
    if (error) return res.status(400).json({ error: error.message });
    const q = `INSERT INTO bids (proposal_id,vendor_name,price_usd,price_bol,days,notes,wallet_address,preferred_stablecoin,milestones,doc,status)
               VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,'pending') RETURNING *`;
    const vals = [
      value.proposalId,
      value.vendorName,
      value.priceUSD,
      value.priceBol,
      value.days,
      value.notes,
      value.walletAddress,
      value.preferredStablecoin,
      JSON.stringify(value.milestones),
      value.doc ? JSON.stringify(value.doc) : null,
    ];
    const { rows } = await pool.query(q, vals);
    res.json(rows[0]);
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get("/bids", async (req, res) => {
  const { rows } = await pool.query("SELECT * FROM bids WHERE proposal_id=$1", [
    req.query.proposalId,
  ]);
  res.json(rows);
});

// ---------- Milestones ----------
app.post("/milestones/:bidId/complete", async (req, res) => {
  try {
    const { bidId } = req.params;
    const { milestoneIndex } = req.body;
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [
      bidId,
    ]);
    const bid = rows[0];
    if (!bid) return res.status(404).json({ error: "Bid not found" });
    const milestones = bid.milestones || [];
    if (!milestones[milestoneIndex])
      return res.status(400).json({ error: "Invalid milestone index" });
    milestones[milestoneIndex].completed = true;
    await pool.query("UPDATE bids SET milestones=$1 WHERE bid_id=$2", [
      JSON.stringify(milestones),
      bidId,
    ]);
    res.json({ ok: true, milestones });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// ---------- Proofs ----------
app.post("/proofs/:bidId", async (req, res) => {
  try {
    const { bidId } = req.params;
    const { proofCid, description } = req.body;
    await pool.query(
      "INSERT INTO proofs (bid_id, proof_cid, description, created_at) VALUES ($1,$2,$3,now())",
      [bidId, proofCid, description]
    );
    res.json({ ok: true });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get("/proofs/:bidId", async (req, res) => {
  const { rows } = await pool.query("SELECT * FROM proofs WHERE bid_id=$1", [
    req.params.bidId,
  ]);
  res.json(rows);
});

// ---------- Payments ----------
app.post("/payments/:bidId/release", async (req, res) => {
  try {
    const { bidId } = req.params;
    const { token } = req.body;
    const { rows } = await pool.query("SELECT * FROM bids WHERE bid_id=$1", [
      bidId,
    ]);
    const bid = rows[0];
    if (!bid) return res.status(404).json({ error: "Bid not found" });

    const total = bid.price_usd;
    const result = await blockchainService.sendToken(
      token,
      bid.wallet_address,
      total
    );
    res.json(result);
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// ---------- IPFS Upload ----------
app.post("/ipfs/upload-file", async (req, res) => {
  try {
    if (!req.files || !req.files.file)
      return res.status(400).json({ error: "No file uploaded" });
    const uploaded = await pinataUploadFile(req.files.file);
    res.json(uploaded);
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// ========== Start ==========
app.listen(PORT, () => {
  console.log(`[api] Listening on :${PORT}`);
});
