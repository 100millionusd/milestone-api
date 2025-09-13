// services/runBidAnalysis.js
const OpenAI = require("openai");

const client = new OpenAI({
  apiKey: process.env.OPENAI_API_KEY,
});

/**
 * Runs AI analysis for a vendor bid.
 * @param {Object} bid - The validated bid object (from Joi schema).
 * @returns {Promise<Object>} Analysis result in JSON.
 */
async function runBidAnalysis(bid) {
  try {
    const prompt = `
    Analyze the following vendor bid and compare it with reference market prices.

    Vendor: ${bid.vendorName}
    Proposal ID: ${bid.proposalId}
    Price (USD): ${bid.priceUSD}
    Duration: ${bid.days} days
    Notes: ${bid.notes || "N/A"}
    Preferred Stablecoin: ${bid.preferredStablecoin}

    Milestones:
    ${bid.milestones.map((m, i) => `${i + 1}. ${m.name} – $${m.amount} by ${m.dueDate}`).join("\n")}

    Please return a JSON array with one entry per item (if possible), using this format:
    [
      {
        "item": "Concrete",
        "vendor_price": 500,
        "reference_price": 450,
        "difference_percent": 11.1,
        "verdict": "Overpriced"
      }
    ]

    If no reference database values are available, do your best guess and clearly state "No reference DB available".
    `;

    const resp = await client.chat.completions.create({
      model: "gpt-4o-mini",
      messages: [{ role: "user", content: prompt }],
      response_format: { type: "json" },
    });

    const raw = resp.choices[0].message?.content || "[]";

    let parsed;
    try {
      parsed = JSON.parse(raw);
    } catch {
      parsed = [{ error: "Failed to parse AI output", raw }];
    }

    return parsed;
  } catch (err) {
    console.error("runBidAnalysis error:", err);
    return [{ error: err.message }];
  }
}

module.exports = { runBidAnalysis };
