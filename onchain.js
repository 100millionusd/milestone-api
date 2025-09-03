// onchain.js — complete router with read endpoints used by the UI
const express = require("express");
const { ethers } = require("ethers");
const path = require("path");
const fs = require("fs");

const router = express.Router();

// --- Provider & signer (reads work without PK; writes need PRIVATE_KEY) ---
const RPC =
  process.env.SEPOLIA_RPC_URL ||
  process.env.LOCAL_RPC_URL ||
  "http://127.0.0.1:8545";
const provider = new ethers.JsonRpcProvider(RPC);
const ESCROW_ADDR = process.env.ESCROW_ADDR;

// Load ABI (from artifacts or inline ABI)
let ABI;
try {
  const p = path.resolve(
    __dirname,
    "../artifacts/contracts/MilestoneEscrow.sol/MilestoneEscrow.json"
  );
  ABI = JSON.parse(fs.readFileSync(p, "utf8")).abi;
} catch {
  // Minimal ABI subset we actually use here
  ABI = [
    "function projects(uint256) view returns (address funder,address vendor,address token,uint256 total,uint256 released,bytes32 proposalHash,bool cancelled)",
    "function milestones(uint256) view returns (tuple(uint256 amount,bytes32 reportHash,bool released)[])",
  ];
}

if (!ESCROW_ADDR) {
  console.warn(
    "[onchain] ESCROW_ADDR not set. Set it to your MilestoneEscrow address."
  );
}

// ---------- READ: project ----------
router.get("/project/:id", async (req, res) => {
  try {
    if (!ESCROW_ADDR) return res.status(500).json({ error: "ESCROW_ADDR missing" });
    const id = BigInt(req.params.id);
    const escrow = new ethers.Contract(ESCROW_ADDR, ABI, provider);

    const p = await escrow.projects(id);
    const result = {
      ok: true,
      id: Number(id),
      project: [
        p.funder,
        p.vendor,
        p.token,
        p.total?.toString?.() ?? "0",
        p.released?.toString?.() ?? "0",
        p.proposalHash,
        Boolean(p.cancelled),
      ],
      addresses: [p.funder, p.vendor, p.token],
    };
    res.json(result);
  } catch (e) {
    res.status(500).json({ error: String(e.message || e) });
  }
});

// ---------- READ: milestones ----------
router.get("/milestones/:id", async (req, res) => {
  try {
    if (!ESCROW_ADDR) return res.status(500).json({ error: "ESCROW_ADDR missing" });
    const id = BigInt(req.params.id);
    const escrow = new ethers.Contract(ESCROW_ADDR, ABI, provider);

    const ms = await escrow.milestones(id);
    const norm = ms.map((m) => [
      m.amount?.toString?.() ?? "0",
      m.reportHash,
      Boolean(m.released),
    ]);

    res.json({ ok: true, id: Number(id), milestones: norm });
  } catch (e) {
    res.status(500).json({ error: String(e.message || e) });
  }
});

module.exports = router;
