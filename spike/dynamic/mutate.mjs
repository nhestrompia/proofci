// Plants wrong translations in the proved functions of Gen/ and checks that Proofs.lean
// then fails. Run in the toolchain image after ./lean.sh has built Gen/ (OUT, default /tmp/dyn-olean).
import fs from "node:fs";
import path from "node:path";
import { execFileSync } from "node:child_process";

const here = path.dirname(new URL(import.meta.url).pathname);
const OUT = process.env.OUT ?? "/tmp/dyn-olean";
const PROVED = {
  Unknown: ["parseChartGroupByFieldId"],
  Fixtures: ["Counter.bump", "bumpBoth"],
  Bank: ["transfer"],
  Slideshow: ["SlideshowHistory.queue"],
};
const KINDS = {
  "add-sub": [/bin \.add\b/g, "bin .sub"],
  "sub-add": [/bin \.sub\b/g, "bin .add"],
  "lt-le": [/bin \.lt\b/g, "bin .le"],
  "le-lt": [/bin \.le\b/g, "bin .lt"],
  "gt-ge": [/bin \.gt\b/g, "bin .ge"],
  "eq-ne": [/bin \.eq\b/g, "bin .ne"],
  number: [/\(num (\d+)\)/g, (_, n) => `(num ${Number(n) + 1})`],
  string: [/\(str "([^"]*)"\)/g, (_, s) => `(str "${s}q")`],
  key: [/\b(field|setField) (\S+) "([^"]*)"/g, (_, f, o, k) => `${f} ${o} "${k}q"`],
  "null-undef": [/\.null\b/g, ".undef"],
  "skip-write": [/\bsetField (\S+) ("[^"]*")/g, (_, o, k) => `(fun _ _ (_ : Val) => (pure () : M Unit)) ${o} ${k}`],
  "not-test": [/\bif truthy\b/g, "if !truthy"],
};
const LP = execFileSync("sh", ["-c", "cd /opt/proofci/spike/core && lake env printenv LEAN_PATH"]).toString().trim();

const results = [];
for (const [mod, names] of Object.entries(PROVED)) {
  const file = path.join(here, "Gen", `${mod}.lean`);
  const text = fs.readFileSync(file, "utf8");
  const lines = text.split("\n");
  const body = new Set();
  let on = false;
  lines.forEach((l, i) => {
    if (/^(def|abbrev|end) /.test(l)) on = names.some((n) => l.startsWith(`def ${n} `));
    else if (on) body.add(i);
  });
  for (const [kind, [re, rep]] of Object.entries(KINDS)) {
    for (const i of body) {
      for (const m of lines[i].matchAll(re)) {
        const mutated = [...lines];
        mutated[i] = lines[i].slice(0, m.index) + m[0].replace(new RegExp(re.source), rep) + lines[i].slice(m.index + m[0].length);
        const dir = fs.mkdtempSync("/tmp/dyn-mut-");
        fs.mkdirSync(path.join(dir, "Gen"));
        fs.writeFileSync(path.join(dir, "Gen", `${mod}.lean`), mutated.join("\n"));
        const env = { ...process.env, LEAN_PATH: `${LP}:${dir}:${OUT}` };
        let ok = true;
        try {
          execFileSync("lean", ["-o", path.join(dir, "Gen", `${mod}.olean`), path.join(dir, "Gen", `${mod}.lean`)], { env, stdio: "pipe" });
          execFileSync("lean", [path.join(here, "Proofs.lean")], { env, stdio: "pipe", cwd: here });
        } catch {
          ok = false;
        }
        results.push({ mod, line: i + 1, kind, caught: !ok });
        console.log(`${ok ? "SURVIVED" : "caught"} ${mod}:${i + 1} ${kind}`);
        fs.rmSync(dir, { recursive: true });
      }
    }
  }
}
const survived = results.filter((r) => !r.caught);
console.log(`${results.length} mutants, ${results.length - survived.length} caught`);
process.exit(survived.length ? 1 : 0);
