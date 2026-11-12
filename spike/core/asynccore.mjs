// Compares Core's reading of async functions (CoreAsync.lean, lowered by lower.mjs) with Node, on scripted
// outside calls: the result or rejection, and the trace of calls, must be the same text on both sides.
// There is no bridge theorem from the Lean view to this layer yet; this is the test that stands in for it.
// usage: node asynccore.mjs <fixture dir with effects.json> <out dir> [cases] [file::name ...]
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { createRequire } from "node:module";
import { pathToFileURL } from "node:url";
import { compile, generator, runAsync } from "../../typescript/differential.mjs";
import { translate } from "../../typescript/translate.mjs";
import { lower } from "./lower.mjs";

const [dirArg, outArg, casesArg, ...named] = process.argv.slice(2);
const root = resolve(dirArg), out = resolve(outArg);
mkdirSync(out, { recursive: true });
const effects = JSON.parse(readFileSync(join(root, "effects.json"), "utf8"));
const ts = createRequire(import.meta.url)("../../typescript/node_modules/typescript");
const exported = file => {
  const source = ts.createSourceFile(file, readFileSync(join(root, file), "utf8"), ts.ScriptTarget.ES2022, true);
  return source.statements.filter(s => ts.isFunctionDeclaration(s) && s.name
    && s.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)).map(s => `${file}::${s.name.text}`);
};
const all = readdirSync(root).filter(f => /\.ts$/.test(f) && !/^(world|types)\.ts$/.test(f)).flatMap(exported);
const wanted = named.length ? named : all;

// Only functions the view and the lowering both accept are compared.
const view = translate({ root, module: "Check", targets: wanted, requireTypes: true, effects });
const targets = wanted.filter(t => !view.failures[t]);
const lowered = [];
for (const t of targets) {
  try { lowered.push([t, lower(root, [t], { eff: { effects } })]); } catch (error) { console.error(`not lowered: ${t}: ${error.message}`); }
}
const { lean, names } = lower(root, lowered.map(([t]) => t), { eff: { effects } });

const bits = new DataView(new ArrayBuffer(8));
const bitsOf = x => { bits.setFloat64(0, x); return bits.getBigUint64(0); };
const codes = s => [...s].map(c => c.charCodeAt(0));
// One text form for a value on both sides, as in mk.mjs.
const show = v => {
  if (v === undefined) return "undefined";
  if (v === null) return "null";
  if (typeof v === "bigint") return `${v}n`;
  if (typeof v === "string") return `s[${codes(v).join(",")}]`;
  if (typeof v === "number") return Number.isNaN(v) ? "NaN" : `#${bitsOf(v)}`;
  if (typeof v !== "object") return String(v);
  if (Array.isArray(v)) return `[${v.map(show).join(",")}]`;
  return `{${Object.keys(v).sort().map(k => `${k}:${show(v[k])}`).join(",")}}`;
};
const data = v => {
  if (v === undefined) return ".leaf .undef";
  if (v === null) return ".leaf .null";
  if (typeof v === "boolean") return `.leaf (.bool ${v})`;
  if (typeof v === "number") return `.leaf (.num (F64.ofBits ${bitsOf(v)}))`;
  if (typeof v === "bigint") return `.leaf (.big (${v}))`;
  if (typeof v === "string") return `.leaf (.str [${codes(v).join(", ")}])`;
  if (Array.isArray(v)) return `.arr [${v.map(x => `(${data(x)})`).join(", ")}]`;
  return `.obj [${Object.entries(v).map(([k, x]) => `(${JSON.stringify(k)}, ${data(x)})`).join(", ")}]`;
};

const compiled = join(out, "js");
compile(root, view.files, view.imports, compiled, view.effectList);
const lines = [lean.trimEnd(), "", "open Core Core.Async Gen", ""];
const expected = [];
let seed = 3;
for (const target of targets.filter(t => lowered.some(([l]) => l === t))) {
  const signature = view.signatures[target];
  const loaded = await import(pathToFileURL(join(compiled, signature.file.replace(/\.ts$/, ".mjs"))));
  const fn = loaded[signature.name];
  const value = generator(seed++);
  for (let i = 0; i < Number(casesArg ?? 30); i += 1) {
    const inputs = signature.params.map(value);
    const { outcome, trace } = await runAsync(fn, structuredClone(inputs), view.effectList, seed * 1000 + i);
    const result = "value" in outcome ? `fulfilled ${show(outcome.value)}`
      : outcome.error instanceof Error ? `rejected {message:${show(outcome.error.message)},name:${show(outcome.error.name)}}` : "?";
    const events = trace.map(c => `${c.id}(${c.args.map(show).join(",")})${c.answer.reject !== undefined ? `->r:s[${codes(c.answer.reject).join(",")}]` : `->v:${show(c.answer.value)}`}`);
    expected.push(`ASYNC ${result}|${events.join(";")}`);
    const script = trace.map(c => `(${JSON.stringify(c.id)}, ${c.answer.reject !== undefined
      ? `Ans.reject [69, 114, 114, 111, 114] [${codes(c.answer.reject).join(", ")}]` : `Ans.value (${data(c.answer.value)})`})`);
    lines.push(`#eval IO.println (report prog aprog (scripted [${script.join(", ")}]) ${names[target]} [${inputs.map(x => `(${data(x)})`).join(", ")}])`);
  }
}
writeFileSync(join(out, "Core.lean"), `${lines.join("\n")}\n`);
writeFileSync(join(out, "expected.json"), JSON.stringify(expected));
console.log(`${targets.length} functions, ${expected.length} cases`);
