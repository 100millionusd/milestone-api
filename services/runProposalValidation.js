// services/runProposalValidation.js
const OpenAI = require("openai");
const fs = require("fs");
const path = require("path");

const client = new OpenAI({
  apiKey: process.env.OPENAI_API_KEY,
});

// Helper: Convert local file to Base64 so the AI can "see" it
function encodeImage(filePath) {
  try {
    const fileBuffer = fs.readFileSync(filePath);
    return fileBuffer.toString("base64");
  } catch (error) {
    console.error(`Error reading file ${filePath}:`, error);
    return null;
  }
}

async function runProposalValidation(proposal) {
  try {
    // 1. Prepare the content array for the User Message
    // We start with the text prompt
    const contentArray = [
      {
        type: "text",
        text: `
        Validate this proposal.
        
        CLAIMED DATA:
        Org: ${proposal.orgName}
        Address: ${proposal.address || "N/A"}
        Budget: $${proposal.amountUSD}

        INSTRUCTIONS:
        1. Look at the attached images/screenshots.
        2. **EXTRACT LOCATION**: specificially look for text indicating a location (like "Potosí, Bolivia" or GPS coordinates) in the pixels of the image.
        3. **COMPARE**: Check if that detected location matches the Claimed Address (${proposal.address}).
        4. Return JSON with keys: { orgValid, addressValid, detectedLocation, locationConsistencyCheck, issues }.
        `
      }
    ];

    // 2. Loop through docs and attach valid images to the payload
    if (proposal.docs && proposal.docs.length > 0) {
      for (const doc of proposal.docs) {
        // Ensure we have a path and it's an image
        if (doc.path && /\.(jpg|jpeg|png|webp)$/i.test(doc.name)) {
          const base64Image = encodeImage(doc.path);
          if (base64Image) {
            contentArray.push({
              type: "image_url",
              image_url: {
                url: `data:image/jpeg;base64,${base64Image}`,
                detail: "high" // "high" allows it to read small text like "Potosí"
              }
            });
          }
        }
      }
    }

    // 3. Send the request with the images included
    const resp = await client.chat.completions.create({
      model: "gpt-4o-mini", // This model supports Vision (images)
      messages: [
        { 
          role: "user", 
          content: contentArray // Sends both Text + Images
        }
      ],
      response_format: { type: "json_object" },
    });

    return JSON.parse(resp.choices[0].message.content || "{}");
  } catch (err) {
    console.error("Validation failed:", err);
    return { error: err.message };
  }
}

module.exports = { runProposalValidation };