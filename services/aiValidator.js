import OpenAI from "openai";
const client = new OpenAI({ apiKey: process.env.OPENAI_API_KEY });

export async function runProposalValidation(proposal) {
  try {
    const textSummary = proposal.summary || "";
    const docs = (proposal.docs || []).map(d => d.name).join(", ");

    const prompt = `
You are an AI validator for project proposals. 
Check the following:

1. Organization name (${proposal.orgName}) — does it look realistic?
2. Address (${proposal.address || "N/A"}) — is it valid and complete?
3. Contact (${proposal.contact || "N/A"}) — does it look correct (email/phone)?
4. Budget: Proposal says $${proposal.amountUSD}. If attachments mention another number, flag mismatch.
5. General issues with attachments: ${docs || "none"}.

Reply in JSON with keys:
{
  "organizationMatch": true/false,
  "addressMatch": true/false,
  "contactValid": true/false,
  "budgetMatch": true/false,
  "issues": [ "list of issues" ]
}
`;

    const resp = await client.chat.completions.create({
      model: "gpt-4o-mini",
      messages: [{ role: "user", content: prompt }],
      response_format: { type: "json_object" }
    });

    return JSON.parse(resp.choices[0].message.content);
  } catch (err) {
    console.error("Validation failed:", err);
    return { error: "Validation failed: " + err.message };
  }
}
