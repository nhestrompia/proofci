// Lowers the sample functions into Spike/Gen.lean and writes Node-vs-Core comparisons
// into Spike/Diff.lean. Inputs deliberately share objects, to exercise the heap.
import { writeFileSync, mkdirSync, cpSync } from "node:fs";
import { dirname, join } from "node:path";
import { execFileSync } from "node:child_process";
import { fileURLToPath, pathToFileURL } from "node:url";
import ts from "../../typescript/node_modules/typescript/lib/typescript.js";
import { lower } from "./lower.mjs";

const here = dirname(fileURLToPath(import.meta.url));
const repo = join(here, "../..");
mkdirSync(join(here, "work/src/config"), { recursive: true });
for (const [from, to] of [["examples/ts-real/src/phases.ts", "src/phases.ts"], ["examples/ts-real/src/config/price.ts", "src/config/price.ts"],
  ["examples/ts-real/src/constants.ts", "src/constants.ts"], ["examples/ts-bank/src/ledger.ts", "src/ledger.ts"], ["spike/core/fixtures/shared.ts", "src/shared.ts"]]) {
  cpSync(join(repo, from), join(here, "work", to));
}
const root = join(here, "work");
const targets = ["src/phases.ts::getActiveSpendingPhase", "src/config/price.ts::deriveAuctionPricing", "src/ledger.ts::transfer", "src/ledger.ts::sumAmounts",
  "src/shared.ts::moveMoney", "src/shared.ts::moveMoneyStale"];
const { names, lean } = lower(root, targets);
writeFileSync(join(here, "Spike/Gen.lean"), lean);

// Compile to JavaScript and load.
const load = async file => {
  const js = ts.transpileModule(ts.sys.readFile(join(root, file)), { compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext } }).outputText
    .replace(/from '\.\.\/constants'/, "from '../constants.mjs'");
  const out = join(root, file.replace(/\.ts$/, ".mjs")); ts.sys.writeFile(out, js);
  return import(pathToFileURL(out));
};
await load("src/constants.ts");
const mods = { phases: await load("src/phases.ts"), price: await load("src/config/price.ts"), ledger: await load("src/ledger.ts"), shared: await load("src/shared.ts") };

// Inputs as Core: objects get heap slots by identity, so sharing is preserved.
function encoder() {
  const seen = new Map(), heap = [];
  const val = v => {
    if (v === undefined) return ".undef";
    if (v === null) return ".null";
    if (typeof v === "boolean") return `(.bool ${v})`;
    if (typeof v === "number") return `(.num (F64.ofBits ${bitsOf(v)}))`;
    if (typeof v === "bigint") return `(.big (${v}))`;
    if (typeof v === "string") return `(.str [${[...v].map(c => c.charCodeAt(0)).join(", ")}])`;
    if (seen.has(v)) return `(.ref ${seen.get(v)})`;
    const slot = heap.length; seen.set(v, slot); heap.push(null);
    heap[slot] = Array.isArray(v) ? `.array [${v.map(val).join(", ")}]` : `.record [${Object.entries(v).map(([k, x]) => `(${JSON.stringify(k)}, ${val(x)})`).join(", ")}]`;
    return `(.ref ${slot})`;
  };
  return { val, heap };
}
const view64 = new DataView(new ArrayBuffer(8));
const bitsOf = x => { view64.setFloat64(0, x); return view64.getBigUint64(0); };
// One text form for a value, the same on both sides. Key order isn't meaningful.
const show = (v, depth = 0) => {
  if (v === undefined) return "undefined";
  if (v === null) return "null";
  if (typeof v === "bigint") return `${v}n`;
  if (typeof v === "string") return `s[${[...v].map(c => c.charCodeAt(0)).join(",")}]`;
  if (typeof v === "number") return Number.isNaN(v) ? "NaN" : `#${bitsOf(v)}`;
  if (typeof v !== "object") return String(v);
  if (Array.isArray(v)) return `[${v.map(x => show(x)).join(",")}]`;
  return `{${Object.keys(v).sort().map(k => `${k}:${show(v[k])}`).join(",")}}`;
};

let seed = 7;
const rand = n => (seed = (seed * 1103515245 + 12345) & 0x7fffffff) % n;
const int = () => rand(41) - 20;
const age = () => (rand(4) === 0 ? null : rand(90));
const phase = i => ({ id: `p${i}`, name: "n", fromAge: age(), annualWithdrawal: int() });
const account = () => ({ balance: int() });
const big = () => { const r = rand(5); return r === 0 ? 0n : BigInt(rand(200000) - 20000) * (r === 1 ? 10n ** 30n : 1n); };

const cases = [];
for (let i = 0; i < 200; i += 1) {
  const n = rand(5);
  const xs = Array.from({ length: n }, (_, j) => phase(j));
  if (n > 1 && rand(2)) xs[1] = xs[0]; // the same object twice
  cases.push(["src/phases.ts::getActiveSpendingPhase", mods.phases.getActiveSpendingPhase, [xs, rand(90)]]);
  cases.push(["src/config/price.ts::deriveAuctionPricing", mods.price.deriveAuctionPricing, [big()]]);
  cases.push(["src/ledger.ts::transfer", mods.ledger.transfer, [{ from: int(), to: int() }, int()]]);
  cases.push(["src/ledger.ts::sumAmounts", mods.ledger.sumAmounts, [Array.from({ length: rand(6) }, int)]]);
  const a = account(), b = rand(2) ? a : account();
  cases.push(["src/shared.ts::moveMoney", mods.shared.moveMoney, [a, b, int()]]);
  const c = account(), d = rand(2) ? c : account();
  cases.push(["src/shared.ts::moveMoneyStale", mods.shared.moveMoneyStale, [c, d, int()]]);
}

const lines = ["import Core", "import Spike.Gen", "import Spike.Show", "open Core Gen Spike", ""];
let expected = [];
for (const [target, fn, args] of cases) {
  const { val, heap } = encoder();
  const encoded = args.map(val);
  // Core is told the state before; Node's mutation only happens below.
  const heapText = `[${heap.join(", ")}]`;
  let out;
  try { out = show(fn(...args)); } catch { out = "throw"; }
  expected.push(`${out}|${args.map(a => show(a)).join("|")}`);
  lines.push(`#eval report ${names[target]} [${encoded.join(", ")}] ${heapText}`);
}
writeFileSync(join(here, "Spike/Diff.lean"), `${lines.join("\n")}\n`);
writeFileSync(join(here, "work/expected.json"), JSON.stringify(expected));
