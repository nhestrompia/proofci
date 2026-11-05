// Node against Core for language features, with the same text form as mk.mjs.
import { writeFileSync, cpSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import ts from "/Users/nhestrompia/.t3/worktrees/proofci/typescript-support/typescript/node_modules/typescript/lib/typescript.js";
import { lower } from "./lower.mjs";
const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, "work");
for (const f of ["prelude", "features", "async"]) cpSync(join(here, `fixtures/${f}.ts`), join(root, `src/${f}.ts`));
const F = ["amountOf", "mapGrows", "mapShrinks", "clamp01", "overrideSeen", "counterTwice", "loopCaptures", "scaled", "indexed", "positives", "total", "anyOver", "firstNegative", "positivesLoop", "sumPlusOne", "dispatch", "growBoth", "treeSum"];
const A = ["withdrawStale", "withdrawSafe", "twoWaits"];
const targets = [...F.map(f => `src/features.ts::${f}`), ...A.map(f => `src/async.ts::${f}`)];
const { names, lean } = lower(root, [...targets, "src/ledger.ts::transfer", "src/ledger.ts::sumAmounts", "src/phases.ts::getActiveSpendingPhase", "src/config/price.ts::deriveAuctionPricing"]);
writeFileSync(join(here, "Spike/Gen.lean"), lean);
const load = async f => { const out = join(root, `${f}.mjs`);
  ts.sys.writeFile(out, ts.transpileModule(ts.sys.readFile(join(root, `src/${f}.ts`)), { compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext } }).outputText);
  return import(pathToFileURL(out)); };
const features = await load("features"), asyncs = await load("async");
const dv = new DataView(new ArrayBuffer(8));
const bitsOf = x => { dv.setFloat64(0, x); return dv.getBigUint64(0); };
const show = v => {
  if (v === undefined) return "undefined";
  if (v === null) return "null";
  if (typeof v === "number") return Number.isNaN(v) ? "NaN" : `#${bitsOf(v)}`;
  if (typeof v === "string") return `s[${[...v].map(c => c.charCodeAt(0)).join(",")}]`;
  if (typeof v !== "object") return String(v);
  if (Array.isArray(v)) return `[${v.map(show).join(",")}]`;
  return `{${Object.keys(v).sort().map(k => `${k}:${show(v[k])}`).join(",")}}`;
};
function encoder() { const seen = new Map(), heap = [];
  const val = v => { if (v === undefined) return ".undef"; if (v === null) return ".null"; if (typeof v === "boolean") return `(.bool ${v})`;
    if (typeof v === "number") return `(.num (F64.ofBits ${bitsOf(v)}))`;
    if (typeof v === "string") return `(.str [${[...v].map(c => c.charCodeAt(0)).join(", ")}])`;
    if (seen.has(v)) return `(.ref ${seen.get(v)})`;
    const slot = heap.length; seen.set(v, slot); heap.push(null);
    heap[slot] = Array.isArray(v) ? `.array [${v.map(val).join(", ")}]` : `.record [${Object.entries(v).map(([k, x]) => `(${JSON.stringify(k)}, ${val(x)})`).join(", ")}]`;
    return `(.ref ${slot})`; };
  return { val, heap }; }
let seed = 11; const rand = n => (seed = (seed * 1103515245 + 12345) & 0x7fffffff) % n;
const num = () => { const r = rand(5); return r === 0 ? (rand(41) - 20) / 4 : r === 1 ? [0, -0, 0.1, 0.2, 1e300, -1e300, NaN, Infinity][rand(8)] : rand(41) - 20; };
const arr = () => Array.from({ length: rand(5) }, num);
const tree = d => (d === 0 || rand(3) === 0) ? null : { value: num(), left: tree(d - 1), right: tree(d - 1) };
const sharedTree = () => { const s = tree(2); return { value: num(), left: s, right: s }; };
const lines = ["import Core", "import Spike.Gen", "import Spike.Show", "open Core Gen Spike", ""]; const expected = [];
const inputs = { amountOf: () => [[num(), "abc", "", null, undefined, true, { a: 1 }][rand(7)]], mapGrows: () => [arr()], mapShrinks: () => [arr()], clamp01: () => [num()], overrideSeen: () => [], counterTwice: () => [num()], loopCaptures: () => [arr()], scaled: () => [arr(), num()], indexed: () => [arr()], positives: () => [arr()], total: () => [arr()],
  anyOver: () => [arr(), num()], firstNegative: () => [arr()], positivesLoop: () => [arr()], sumPlusOne: () => [arr()], dispatch: () => [num()], growBoth: () => [num()], treeSum: () => [rand(2) ? sharedTree() : tree(3)] };
for (const f of F) for (let i = 0; i < 60; i += 1) {
  const args = inputs[f](); const { val, heap } = encoder(); const enc = args.map(val);
  let out; try { out = show(features[f](...args)); } catch { out = "throw"; }
  expected.push(`${f}: ${out}`);
  lines.push(`#eval IO.println ("${f}: " ++ result ${names[`src/features.ts::${f}`]} [${enc.join(", ")}] [${heap.join(", ")}])`);
}
for (const [fa, fb] of [["withdrawStale", "withdrawStale"], ["withdrawSafe", "withdrawSafe"], ["withdrawStale", "withdrawSafe"], ["twoWaits", "withdrawSafe"], ["twoWaits", "twoWaits"]]) for (let i = 0; i < 12; i += 1) {
  const acct = { balance: rand(100), log: [] }, x = rand(20) + 1, y = rand(20) + 1;
  const { val, heap } = encoder(); const v = val(acct); const hs = `[${heap.join(", ")}]`;
  await Promise.all([asyncs[fa](acct, x), asyncs[fb](acct, y)]);
  expected.push(`async: ${show(acct)}`);
  lines.push(`#eval IO.println ("async: " ++ resultAsync [(Gen.src_async_${fa}_segs, ["a", "amount"], [${v}, (.num (F64.ofInt ${x}))]), (Gen.src_async_${fb}_segs, ["a", "amount"], [${v}, (.num (F64.ofInt ${y}))])] ${hs} ${v})`);
}
writeFileSync(join(here, "Spike/Diff2.lean"), `${lines.join("\n")}\n`);
writeFileSync(join(root, "expected2.json"), JSON.stringify(expected));
