// Compares `Object.keys` in Core with Node on generated objects: a literal, then writes to new
// and existing keys. Writes <dir>/Keys.lean (one #eval per case) and <dir>/expected.json;
// `node keyscheck.mjs compare <dir> <output of lake env lean Keys.lean>` counts the results.
import { writeFileSync, readFileSync, mkdirSync } from "node:fs";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import ts from "../../typescript/node_modules/typescript/lib/typescript.js";
import { lower } from "./lower.mjs";

const [mode, dir, leanOut] = process.argv.slice(2);
if (mode === "compare") {
  const expected = JSON.parse(readFileSync(join(dir, "expected.json"), "utf8"));
  const got = readFileSync(leanOut, "utf8").split("\n").filter(l => l.startsWith("K "));
  let agree = 0, left = 0;
  const differ = [];
  expected.forEach((e, i) => {
    const g = got[i]?.slice(2);
    if (g === "stuck") left += 1;
    else if (g === e) agree += 1;
    else differ.push([i, e, g]);
  });
  console.log(`${agree} agree, ${left} left the model, ${differ.length} differ`);
  for (const d of differ.slice(0, 5)) console.log(d);
  process.exit(differ.length || got.length !== expected.length ? 1 : 0);
}

let seed = 11;
const rand = n => (seed = (seed * 1103515245 + 12345) & 0x7fffffff) % n;
const NAMES = ["a", "b", "c", "zz", "_x", "$y", "é"];
const LITERAL = [...NAMES, "1", "07", "x y"];
const fns = [];
for (let i = 0; i < 300; i += 1) {
  const lit = Array.from({ length: rand(4) }, () => LITERAL[rand(LITERAL.length)]);
  const fields = [...new Set(lit)].map((k, j) => `${JSON.stringify(k)}: ${j}`);
  const writes = Array.from({ length: rand(5) }, () => `  o.${NAMES[rand(NAMES.length)]} = a;`);
  fns.push(`export function k${i}(a: number): string {\n  const o: { [k: string]: number } = { ${fields.join(", ")} };\n${writes.join("\n")}\n  return Object.keys(o).join(",");\n}`);
}
const root = join(dir, "work");
mkdirSync(join(root, "src"), { recursive: true });
const source = fns.join("\n\n") + "\n";
writeFileSync(join(root, "src/keys.ts"), source);
const targets = fns.map((_, i) => `src/keys.ts::k${i}`);
const { names, lean } = lower(root, targets);
const js = ts.transpileModule(source, { compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext } }).outputText;
writeFileSync(join(root, "keys.mjs"), js);
const mod = await import(pathToFileURL(join(root, "keys.mjs")));
const text = s => `s[${[...s].map((_, j) => s.charCodeAt(j)).join(",")}]`;
const expected = targets.map((_, i) => text(mod[`k${i}`](5)));
const body = lean.replace("namespace Gen", "namespace KeysGen").replace("end Gen", "end KeysGen");
const evals = targets.map(t => `#eval IO.println ("K " ++ match run 2000 KeysGen.prog KeysGen.${names[t]} [.num (F64.ofInt 5)] [] with
  | .ok (.str s) _ => "s[" ++ ",".intercalate (s.map toString) ++ "]" | .ok _ _ => "other" | .thrown _ _ => "throw" | .stuck => "stuck")`);
writeFileSync(join(dir, "Keys.lean"), `${body}\nopen KeysGen\n${evals.join("\n")}\n`);
writeFileSync(join(dir, "expected.json"), JSON.stringify(expected));
console.log(`${targets.length} cases`);
