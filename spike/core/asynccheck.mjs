// Compares the Lean view of async functions with Node, against scripted outside calls.
//
// Node runs the real function with stand-ins for the effects, which answer from a random script
// (values of the declared type, or rejections) after a random number of turns of the event loop.
// The Lean view then runs with an oracle that replays the same answers. The result (value or
// rejection payload) and the trace of outside calls must agree. Nothing here touches real I/O.
//
// usage: node asynccheck.mjs <fixture dir with effects.json> <out dir> [cases] [file::name ...]
// writes <out>/Check.lean: the translation followed by one #eval per case.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { differential } from "../../typescript/differential.mjs";
import { translate } from "../../typescript/translate.mjs";
import { createRequire } from "node:module";

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
const targets = named.length ? named : readdirSync(root).filter(f => /\.ts$/.test(f) && !/^(world|types)\.ts$/.test(f)).flatMap(exported);
const translated = translate({ root, module: "Check", targets, requireTypes: true, effects });
if (translated.fatal) throw new Error(translated.fatal);
const rejected = Object.entries(translated.failures);
for (const [target, reason] of rejected) console.error(`not translated: ${target}: ${reason}`);
const signatures = Object.fromEntries(Object.entries(translated.signatures));
const { skipped } = await differential({
  root, out, module: "Check", signatures, files: translated.files, imports: translated.imports,
  cases: Number(casesArg ?? 40), effects: translated.effectList,
});
for (const s of skipped) console.error(`skipped: ${s}`);
const replay = readFileSync(join(out, "Differential.lean"), "utf8").split("\n").filter(l => l.startsWith("#eval"));
writeFileSync(join(out, "Check.lean"), `${translated.source.trimEnd()}\n\n${replay.join("\n")}\n`);
writeFileSync(join(out, "targets.json"), JSON.stringify({ translated: Object.keys(signatures), rejected: rejected.map(([t]) => t) }));
console.log(`${Object.keys(signatures).length} functions, ${replay.length} cases`);
