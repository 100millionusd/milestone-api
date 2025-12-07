// services/eventSync.mjs
import { createPublicClient, http } from "viem";
import { sepolia } from "viem/chains";

// REQUIRED ENVs:
//   SEPOLIA_RPC_URL        (https://... from Infura/Alchemy/etc.)
//   CONTRACT_ADDRESS       (0x...)
// OPTIONAL:
//   EVENT_TOPIC0           (0x keccak of the event signature to filter)
//   ENABLE_EVENT_SYNC      (set to "false" to disable)

const RPC_URL = process.env.SEPOLIA_RPC_URL;
const CONTRACT_ADDRESS = process.env.CONTRACT_ADDRESS;
const TOPIC0 = process.env.EVENT_TOPIC0 || null;

if (!RPC_URL) throw new Error("Missing SEPOLIA_RPC_URL");
if (!CONTRACT_ADDRESS) throw new Error("Missing CONTRACT_ADDRESS");

const CONFIRMATIONS = 5n;   // reorg safety
const CHUNK = 2000n;        // range size per getLogs

const client = createPublicClient({ chain: sepolia, transport: http(RPC_URL) });

// In-memory state (swap to DB if you want durability)
let lastProcessedBlock = null; // bigint
const seen = new Set();        // txHash:logIndex dedupe

function logKey(log) {
  return `${log.transactionHash}:${log.logIndex}`;
}

async function safeHead() {
  const head = await client.getBlockNumber();
  return head > (CONFIRMATIONS - 1n) ? head - (CONFIRMATIONS - 1n) : 0n;
}

async function processLogs(logs) {
  for (const log of logs) {
    const key = logKey(log);
    if (seen.has(key)) continue;

    // TODO: decode & persist as needed
    // console.log("[eventSync]", String(log.blockNumber), log.transactionHash, log.logIndex);

    seen.add(key);
  }
}

async function backfill(fromBlock, toBlock) {
  if (toBlock < fromBlock) return;
  for (let from = fromBlock; from <= toBlock; from += CHUNK) {
    const to = (from + CHUNK - 1n) > toBlock ? toBlock : (from + CHUNK - 1n);
    const logs = await client.getLogs({
      address: CONTRACT_ADDRESS,
      topics: TOPIC0 ? [TOPIC0] : undefined,
      fromBlock: from,
      toBlock: to,
    });
    await processLogs(logs);
    lastProcessedBlock = to;
  }
}

export async function startEventSync() {
  const head = await client.getBlockNumber();
  if (lastProcessedBlock == null) {
    const init = head > (CONFIRMATIONS + 5n) ? head - (CONFIRMATIONS + 5n) : 0n;
    lastProcessedBlock = init;
  }

  // Initial catch-up
  await backfill(lastProcessedBlock + 1n, await safeHead());

  // Live loop — always backfills the full gap, so no “skipping block events”
  client.watchBlocks({
    emitOnBegin: true,
    emitMissed: false,
    onBlock: async () => {
      try {
        await backfill((lastProcessedBlock ?? 0n) + 1n, await safeHead());
      } catch (err) {
        // console.error("[eventSync] error", err);
      }
    },
  });

  // console.log("[eventSync] started");
}
