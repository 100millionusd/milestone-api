// services/runProposalValidation.js
const OpenAI = require("openai");

const client = new OpenAI({
  apiKey: process.env.OPENAI_API_KEY,
});

async function runProposalValidation(proposal) {
  try {
    const docs = (proposal.docs || []).map(d => d.name).join(", ");
    const prompt = `
    Validate proposal:
    Org: ${proposal.orgName}
    Address: ${proposal.address || "N/A"}
    Contact: ${proposal.contact || "N/A"}
    Budget: $${proposal.amountUSD}
    Attachments: ${docs || "none"}
    Return JSON with: { orgValid, addressValid, budgetCheck, issues }
    `;

    const resp = await client.chat.completions.create({
      model: "gpt-4o-mini",
      messages: [{ role: "user", content: prompt }],
      response_format: { type: "json_object" },
    });

    return JSON.parse(resp.choices[0].message.content || "{}");
  } catch (err) {
    console.error("Validation failed:", err);
    return { error: err.message };
  }
}

module.exports = { runProposalValidation };
