// Writes one Lean file per function: its typed view from the production translator, its
// dynamic translation from dyn.mjs, and a theorem that a typed result is the dynamic result.
// The proof is the same text for every function.
//
// usage: node bridge.mjs <list.tsv> <outDir>   (rows: repo, file, function; repos under CORPUS)
import { mkdirSync, writeFileSync, readFileSync, readdirSync, rmSync } from "node:fs";
import path from "node:path";
import { translate as typedView } from "../../typescript/translate.mjs";
import { workspacePaths } from "../../typescript/paths.mjs";
import { translate as dynTranslate } from "./dyn.mjs";

const NUL = { null: ".null", undefined: ".undef" };
const short = (n) => n.replace(/[^A-Za-z0-9_]/g, "_");

function plain(t) {
  switch (t.kind) {
    case "number": return "Js.Num";
    case "string": return "(List Nat)";
    case "boolean": return "Bool";
    case "record": return t.lean;
    case "array": return `(List ${plain(t.item)})`;
    case "optional": if (t.both) throw new Error("no encoding for null-or-undefined"); return `(Option ${plain(t.inner)})`;
    default: throw new Error(`no encoding for ${t.kind}`);
  }
}
const crepOf = (t, a, v, h) => t.kind === "optional" ? `crepOpt ${NUL[t.nothing]} ${h} ${a} ${v}` : `crep ${h} ${a} ${v}`;

function records(sig) {
  const out = new Map();
  const scan = (t) => {
    if (t.kind === "record" && !out.has(t.lean)) { t.fields.forEach((f) => scan(f.type)); out.set(t.lean, t); }
    if (t.kind === "optional") scan(t.inner);
    if (t.kind === "array") scan(t.item);
  };
  sig.params.forEach(scan); scan(sig.result);
  return [...out.values()];
}

function recordRules(t) {
  const body = (h, a, v) => `∃ l fs, ${v} = .ref l ∧ ${h}[l]? = some (.record fs) ∧ ${t.fields.map((f) => {
    plain(f.type);
    return `(∃ w, fs.lookup ${JSON.stringify(f.name)} = some w ∧ ${crepOf(f.type, `${a}.«${f.name}»`, "w", h)})`;
  }).join(" ∧ ")}`;
  return `instance : CRep ${t.lean} := ⟨fun h a v => ${body("h", "a", "v")}⟩
theorem crep_${short(t.lean)} {h : Core.Heap} {a : ${t.lean}} {v} : crep h a v ↔ ${body("h", "a", "v")} := Iff.rfl`;
}

export function generate(root, file, fn) {
  const target = `${file}::${fn}`;
  const view = typedView({ root, module: "V", paths: workspacePaths(root), targets: [target], requireTypes: true });
  if (view.failures[target]) throw new Error(`typed path rejects it: ${view.failures[target]}`);
  const sig = view.signatures[target];
  const dyn = dynTranslate(path.join(root, file), [fn]);
  const recs = records(sig);
  const P = sig.params.map((_, i) => `p${i}`), V = sig.params.map((_, i) => `v${i}`);
  const crepNames = ["crep_num", "crep_bool", "crep_str", "crep_list", "crepOpt_some", "crepOpt_none", ...recs.map((t) => `crep_${short(t.lean)}`)].join(", ");
  const hyps = sig.params.map((t, i) => `(h${i} : ${crepOf(t, P[i], V[i], "h")})`).join(" ");
  const source = view.source.replace(/^import.*\n/gm, "").replace(/^open .*\n/gm, "");
  const key = short(sig.lean);
  const text = `import Bridge
open Core Dyn Aeneas Aeneas.Std Result
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

${source}

namespace D
open Core Dyn
${[...dyn.defs.values()].join("\n")}
end D

${recs.map(recordRules).join("\n\n")}

theorem ${key}_dyn {h : Core.Heap} ${V.map((v) => `{${v} : Core.Val}`).join(" ")} ${sig.params.map((t, i) => `{${P[i]} : ${plain(t)}}`).join(" ")} {r : ${plain(sig.result)}}
    ${hyps} (hr : ${sig.lean} ${P.join(" ")} = ok r) :
    Spec (D.${fn} ${V.join(" ")}) h fun v h' => h <+: h' ∧ ${crepOf(sig.result, "r", "v", "h'")} := by
  ${sig.params.length ? `try simp only [${crepNames}] at ${sig.params.map((_, i) => `h${i}`).join(" ")}
  try casesm* ∃ _, _, _ ∧ _
  try subst_vars
  ` : ""}unfold ${sig.lean} at hr
  unfold D.${fn}
  tsteps
  all_goals dsteps
  all_goals first | omega | (refine ⟨by first | exact List.prefix_refl _ | exact List.prefix_append _ _, ?_⟩; simp [${crepNames}, List.lookup, *])

#print axioms ${key}_dyn
`;
  return { text, key, typedDef: sig.lean };
}

if (process.argv[1] === new URL(import.meta.url).pathname) {
  const [list, outDir] = process.argv.slice(2);
  mkdirSync(outDir, { recursive: true });
  for (const f of readdirSync(outDir)) if (/^B\d+\.lean$/.test(f)) rmSync(path.join(outDir, f));
  const rows = readFileSync(list, "utf8").trim().split("\n").map((l) => l.split("\t"));
  const index = [];
  rows.forEach(([repo, file, fn], i) => {
    const root = path.join(process.env.CORPUS ?? `${process.env.HOME}/corpus`, repo);
    try {
      const { text, key, typedDef } = generate(root, file, fn);
      writeFileSync(path.join(outDir, `B${i}.lean`), text);
      index.push({ i, repo, file, fn, key, typedDef, ok: true });
    } catch (e) {
      index.push({ i, repo, file, fn, ok: false, reason: String(e.message).split("\n")[0].slice(0, 160) });
    }
  });
  writeFileSync(path.join(outDir, "index.json"), JSON.stringify(index, null, 1));
  const bad = index.filter((x) => !x.ok);
  console.log(`${index.length - bad.length} generated, ${bad.length} not`);
  for (const b of bad) console.log(`  ${b.fn}: ${b.reason}`);
}
