// The typed view: exactly what ProofCI's translator emits today.
import { writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
const { translate } = await import("../../typescript/translate.mjs");
const here = dirname(fileURLToPath(import.meta.url));
const targets = process.argv.length > 2 ? process.argv.slice(2) : ["src/phases.ts::getActiveSpendingPhase", "src/config/price.ts::deriveAuctionPricing", "src/ledger.ts::transfer", "src/ledger.ts::sumAmounts"];
const r = translate({ root: join(here, "work"), module: "View", targets });
console.error(JSON.stringify(r.failures));
writeFileSync(join(here, "Spike/View.lean"), r.source);
