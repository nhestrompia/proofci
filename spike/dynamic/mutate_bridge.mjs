// Plants wrong translations in the typed view of each proved bridge and checks that the
// bridge then fails. Run in the toolchain image after ./bridgecheck.sh (OUT holds Bridge.olean).
// usage: node mutate_bridge.mjs <dir> [<file>...]
import fs from "node:fs";
import path from "node:path";
import { execFileSync } from "node:child_process";

const here = path.dirname(new URL(import.meta.url).pathname);
const OUT = process.env.OUT ?? "/tmp/dyn-olean";
const LP = execFileSync("sh", ["-c", `cd ${process.env.CORE ?? "/opt/proofci/spike/core"} && lake env printenv LEAN_PATH`]).toString().trim();
const KINDS = {
  "add-sub": [/Js\.add\b/g, "Js.sub"],
  "sub-add": [/Js\.sub\b/g, "Js.add"],
  "mul-add": [/Js\.mul\b/g, "Js.add"],
  "le-lt": [/ ≤ /g, " < "],
  "lt-le": [/ < /g, " ≤ "],
  "gt-ge": [/ > /g, " ≥ "],
  "ge-gt": [/ ≥ /g, " > "],
  "or-and": [/ ∨ /g, " ∧ "],
  "and-or": [/ ∧ /g, " ∨ "],
  number: [/\bJs\.Num\.mk \((-?\d+)\)/g, (_, n) => `Js.Num.mk (${Number(n) + 1})`],
  "true-false": [/\btrue\b/g, "false"],
  "false-true": [/\bfalse\b/g, "true"],
  "none-some": [/Result\.ok none/g, "Result.ok (some default)"],
  "swap-args": [/\bJs\.(sub|div|floorDiv) (\S+) (\S+)/g, (_, op, a, b) => `Js.${op} ${b} ${a}`],
  "drop-op": [/\bJs\.(add|sub|mul) (\S+) (\S+)/g, (_, op, a) => `Result.ok ${a}`],
  "swap-field": [/«from»|«to»/g, (m) => (m === "«from»" ? "«to»" : "«from»")],
  "string": [/js!"([^"]*)"/g, (_, t) => `js!"${t}x"`],
  "rem-floor": [/\bJs\.rem\b/g, "Js.floorDiv"],
  "floor-ceil": [/\bJs\.floorDiv\b/g, "Js.ceilDiv"],
  "ceil-floor": [/\bJs\.ceilDiv\b/g, "Js.floorDiv"],
  "trunc-floor": [/\bJs\.truncDiv\b/g, "Js.floorDiv"],
  "drop-neg": [/\bJs\.neg (\S+)/g, (_, a) => `Result.ok ${a}`],
  "min-max": [/\bJs\.min\b/g, "Js.max"],
};
const [dir, ...only] = process.argv.slice(2);
const index = JSON.parse(fs.readFileSync(path.join(dir, "index.json"), "utf8"));
const results = [];
for (const row of index.filter((r) => r.ok && (!only.length || only.includes(`B${r.i}.lean`)))) {
  const file = path.join(dir, `B${row.i}.lean`);
  const lines = fs.readFileSync(file, "utf8").split("\n");
  const start = lines.findIndex((l) => l.startsWith(`def ${row.typedDef} `));
  if (start < 0) continue;
  let end = start + 1;
  while (end < lines.length && lines[end].trim() !== "") end++;
  for (const [kind, [re, rep]] of Object.entries(KINDS)) {
    for (let i = start + 1; i < end; i++) {
      for (const m of lines[i].matchAll(re)) {
        const mutated = [...lines];
        mutated[i] = lines[i].slice(0, m.index) + m[0].replace(new RegExp(re.source), rep) + lines[i].slice(m.index + m[0].length);
        const tmp = path.join("/tmp", `mut-${row.i}-${kind}-${i}-${m.index}.lean`);
        fs.writeFileSync(tmp, mutated.join("\n"));
        let caught = false;
        try {
          const out = execFileSync("timeout", ["90", "lean", tmp], { env: { ...process.env, LEAN_PATH: `${LP}:${OUT}` }, stdio: "pipe", cwd: here }).toString();
          caught = /error/.test(out);
        } catch { caught = true; }
        fs.rmSync(tmp);
        results.push({ fn: row.fn, kind, caught });
        console.log(`${caught ? "caught" : "SURVIVED"} ${row.fn} ${kind} line ${i + 1}`);
      }
    }
  }
}
const survived = results.filter((r) => !r.caught);
console.log(`${results.length} mutants, ${results.length - survived.length} caught`);
process.exit(survived.length ? 1 : 0);
