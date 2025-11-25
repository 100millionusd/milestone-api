// services/runProposalValidation.js
const OpenAI = require("openai");

const client = new OpenAI({
  apiKey: process.env.OPENAI_API_KEY,
});

async function runProposalValidation(proposal) {
  try {
    const docs = (proposal.docs || []).map(d => d.name).join(", ");
    const detectedLocation = proposal.submissionLocation || "Unknown / Not detected";

    const prompt = `
    You are a strict validation agent. Validate this proposal:

    --- CLAIMED DATA ---
    Org Name: ${proposal.orgName}
    Address: ${proposal.address || "N/A"}
    Contact Email: ${proposal.contact || "N/A"}
    Budget: $${proposal.amountUSD}
    
    --- EVIDENCE ---
    Attachments: ${docs || "none"}
    Detected GPS Location: ${detectedLocation}

    --- INSTRUCTIONS ---
    1. **Org Existence Check**: 
       - Check if the 'Org Name' matches the 'Contact Email' domain (e.g., Org "Heitaria" vs email "...@heitaria.ch"). If they match, it is likely real.
       - If the Org Name looks like a typo (e.g. "fty", "test") or is generic (e.g. "gmail.com"), flag it as 'Suspicious'.
       - Check your internal knowledge base: Is this a known NGO or company?
    
    2. **Location Consistency**: 
       - Compare 'Address' vs 'Detected GPS Location'. 
       - Flag if they are in different countries.

    3. **Return JSON** strictly.

    Output JSON format: 
    { 
      "orgValid": boolean, 
      "orgExistenceCheck": "string (comment on if it looks real/fake)", 
      "addressValid": boolean, 
      "locationConsistencyCheck": "string (pass/fail analysis)", 
      "issues": ["list", "of", "issues"] 
    }
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
