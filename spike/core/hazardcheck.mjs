// The negative control for the hazard rule (typescript/hazard.mjs).
//
// A function that reads shared state after an `await` is refused by the translator. This runs the
// same code in Node, two calls at once, and shows the refusal is warranted: updates are lost, which
// no sequence of outside answers could explain. A function the rule accepts gives the same answer
// under every schedule, so its sequential reading is right.
//
// usage: node hazardcheck.mjs
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { createRequire } from "node:module";
import { translate } from "../../typescript/translate.mjs";

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, "fixtures/hazard");
const ts = createRequire(import.meta.url)("../../typescript/node_modules/typescript");
const effects = JSON.parse(readFileSync(join(root, "effects.json"), "utf8"));

const reasons = {};
for (const name of ["recordAdvance", "countCalls", "recordOnce", "capFor", "capAfterRaise"]) {
  const r = translate({ root, module: "H", targets: [`hazard.ts::${name}`], requireTypes: true, effects });
  reasons[name] = r.failures[`hazard.ts::${name}`] ?? null;
}
console.log("translator:", JSON.stringify(reasons, null, 1));
const refused = ["recordAdvance", "countCalls"].every(n => /module-level/.test(reasons[n] ?? ""));
const accepted = reasons.recordOnce === null && reasons.capFor === null; // a table nothing writes is fine
const touched = /module-level/.test(reasons.capAfterRaise ?? ""); // one that `raise` writes is not

// Run each function in Node, several calls at once, with a world that answers after random delays.
const out = join(here, "work/hazard");
mkdirSync(out, { recursive: true });
const js = ts.transpileModule(readFileSync(join(root, "hazard.ts"), "utf8"), {
  compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext } }).outputText
  .replace('from "./world"', 'from "./world.mjs"');
writeFileSync(join(out, "hazard.mjs"), js);
writeFileSync(join(out, "world.mjs"), "export function save(id, name) { return globalThis.__world(id, name); }\n");
const loaded = await import(pathToFileURL(join(out, "hazard.mjs")));
let seed = 1;
const random = () => { seed = (seed * 48271) % 2147483647; return seed / 2147483647; };
globalThis.__world = () => new Promise(resolve => setTimeout(resolve, Math.floor(random() * 3)));

async function together(name, args, copies) {
  return Promise.all(Array.from({ length: copies }, (_, i) => loaded[name](...args(i))));
}
const runs = 200;
let lost = 0, conservative = 0, stable = 0;
let top = 0;
for (let i = 0; i < runs; i += 1) {
  const a = await together("recordAdvance", k => [`g${k}`], 2);
  if (Math.max(...a) < top + 2) lost += 1;       // two advances were recorded as one
  top = Math.max(...a);
}
for (let i = 0; i < runs; i += 1) {
  const before = await loaded.countCalls("sequential");
  const after = await together("countCalls", k => [`g${k}`], 2);
  if (Math.min(...after) === before + 1 && Math.max(...after) === before + 2) conservative += 1;
}
for (let i = 0; i < runs; i += 1) {
  const sequential = [await loaded.recordOnce("a", 5), await loaded.recordOnce("b", 7)];
  const concurrent = await Promise.all([loaded.recordOnce("a", 5), loaded.recordOnce("b", 7)]);
  if (JSON.stringify(sequential) === JSON.stringify(concurrent)) stable += 1;
}
// The table `raise` writes: the answer follows when `raise` ran, not the outside answers.
let seen = 0;
for (let i = 0; i < runs; i += 1) {
  const before = (await loaded.capAfterRaise("probe"));
  const pending = loaded.capAfterRaise("a");
  loaded.raise();
  if ((await pending) === before + 1) seen += 1;
}
let tableStable = 0;
for (let i = 0; i < runs; i += 1) {
  const sequential = [await loaded.capFor("a", "free"), await loaded.capFor("b", "pro")];
  const concurrent = await Promise.all([loaded.capFor("a", "free"), loaded.capFor("b", "pro")]);
  if (JSON.stringify(sequential) === JSON.stringify(concurrent)) tableStable += 1;
}
console.log(`a table that raise() writes was seen changing under a pending call in ${seen} of ${runs}; the table nothing writes agreed with the sequential reading in ${tableStable}`);
console.log(`Node, two calls at once, ${runs} runs each: recordAdvance lost an update in ${lost}; `
  + `countCalls (refused too, its update is atomic after the await, so the rule is conservative there) stayed correct in ${conservative}; `
  + `recordOnce agreed with the sequential reading in ${stable}`);
const ok = refused && accepted && touched && lost > runs * 0.9 && stable === runs && seen === runs && tableStable === runs;
console.log(ok ? "negative control holds: the lost-update pattern is refused and does lose updates in Node; the accepted function is schedule-independent" : "NEGATIVE CONTROL FAILED");
process.exit(ok ? 0 : 1);
