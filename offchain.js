// ~/Desktop/api/offchain.js
module.exports = function wireOffchain(app) {
  // In-memory stores (demo only)
  const proposals = new Map(); // key: cid -> { cid, orgName, title, summary, contactEmail, status, submittedAt }
  const bids = new Map();      // key: bidId -> { bidId, proposalCid, vendorName, contact, wallet, milestones, docs, createdAt }
  let bidSeq = 1;

  // Queue a proposal for review AFTER you got a CID from /proposal
  app.post("/admin/proposals/queue", (req, res) => {
    const { cid, orgName, title, summary, contactEmail } = req.body || {};
    if (!cid || !orgName || !title || !summary) {
      return res.status(400).json({ error: "cid, orgName, title, summary required" });
    }
    proposals.set(cid, {
      cid, orgName, title, summary, contactEmail: contactEmail || "",
      status: "pending",
      submittedAt: Date.now()
    });
    res.json({ ok: true, cid });
  });

  // List proposals by status
  app.get("/admin/proposals", (req, res) => {
    const status = (req.query.status || "pending").toString();
    const items = [...proposals.values()].filter(p => p.status === status);
    res.json({ ok: true, status, items });
  });

  // Approve / Reject
  app.post("/admin/proposals/:cid/approve", (req, res) => {
    const p = proposals.get(req.params.cid);
    if (!p) return res.status(404).json({ error: "unknown cid" });
    p.status = "approved";
    res.json({ ok: true, cid: p.cid });
  });

  app.post("/admin/proposals/:cid/reject", (req, res) => {
    const p = proposals.get(req.params.cid);
    if (!p) return res.status(404).json({ error: "unknown cid" });
    p.status = "rejected";
    res.json({ ok: true, cid: p.cid });
  });

  // Vendor bids (off-chain)
  app.post("/bids", (req, res) => {
    const { proposalCid, vendorName, contact, wallet, milestones, docs } = req.body || {};
    if (!proposalCid || !vendorName || !milestones || !Array.isArray(milestones) || milestones.length === 0) {
      return res.status(400).json({ error: "proposalCid, vendorName, milestones[] required" });
    }
    const bidId = bidSeq++;
    bids.set(bidId, {
      bidId, proposalCid, vendorName,
      contact: contact || "", wallet: wallet || "",
      milestones, docs: docs || [], createdAt: Date.now()
    });
    res.json({ ok: true, bidId });
  });

  app.get("/bids", (req, res) => {
    const proposalCid = (req.query.proposalCid || "").toString();
    const items = proposalCid
      ? [...bids.values()].filter(b => b.proposalCid === proposalCid)
      : [...bids.values()];
    res.json({ ok: true, items });
  });

  // Handy detail endpoints
  app.get("/admin/proposals/:cid", (req, res) => {
    const p = proposals.get(req.params.cid);
    if (!p) return res.status(404).json({ error: "unknown cid" });
    res.json(p);
  });

  app.get("/bids/:bidId", (req, res) => {
    const b = bids.get(Number(req.params.bidId));
    if (!b) return res.status(404).json({ error: "unknown bid" });
    res.json(b);
  });
};
