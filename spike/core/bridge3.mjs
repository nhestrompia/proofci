// Writes one Lean file per function: its typed view, its Core, and a bridge theorem proved
// by the shared tactics. Nothing here depends on which function it is given.
import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { lower } from "./lower.mjs";
import { translate } from "../../typescript/translate.mjs";
import { workspacePaths } from "../../typescript/survey/analyze.mjs";

const here = dirname(fileURLToPath(import.meta.url));
const units = t => `[${[...Array(t.length).keys()].map(i => t.charCodeAt(i)).join(", ")}]`;
const q = JSON.stringify;
const short = n => n.replace(/[^A-Za-z0-9_]/g, "_");

function leanType(t) {
  switch (t.kind) {
    case "number": return "Js.Num";
    case "string": return "Js.Str";
    case "boolean": return "Bool";
    case "bigint": return "Int";
    case "record": case "enum": return t.lean;
    case "array": return `(List ${leanType(t.item)})`;
    case "optional": return `(Opt ${t.both ? ".both" : t.nothing === "null" ? ".null" : ".undef"} ${leanType(t.inner)})`;
    default: throw new Error(`no encoding for ${t.kind}`);
  }
}

// The same type without the encoding marker: what the typed view itself uses.
const plain = t => t.kind === "optional" ? `(Option ${plain(t.inner)})` : t.kind === "array" ? `(List ${plain(t.item)})` : leanType(t);

// Key lists of record literals, reading nested ones separately.
function recordShapes(lean) {
  const shapes = new Set();
  for (let at = lean.indexOf(".record ["); at >= 0; at = lean.indexOf(".record [", at + 1)) {
    let i = at + 8, depth = 0, str = false;
    const keys = [];
    for (; i < lean.length; i++) {
      const c = lean[i];
      if (str) { if (c === '"') str = false; continue; }
      if (c === '"') {
        if (depth === 2 && lean[i - 1] === "(") keys.push(JSON.parse(lean.slice(i, lean.indexOf('"', i + 1) + 1)));
        str = true;
      } else if ("[(".includes(c)) depth++;
      else if ("])".includes(c)) { depth--; if (depth === 0) break; }
    }
    if (keys.length) shapes.add(JSON.stringify(keys));
  }
  return [...shapes].map(k => JSON.parse(k));
}

function enumRules(e) {
  const n = short(e.lean);
  const tag = `${n}_tag`;
  return `def ${tag} : ${e.lean} → List Nat
${e.tags.map(t => `  | .${t.lean} => ${units(t.tag)}`).join("\n")}
instance : TyRep ${e.lean} := ⟨fun _ a v => v = .str (${tag} a), fun _ h => h⟩
instance : NotNull ${e.lean} := ⟨by rintro _ _ _ rfl; rfl⟩
theorem ${n}_inj {a b : ${e.lean}} (h : ${tag} a = ${tag} b) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [${tag}] at h)
theorem ${n}_iff {a b : ${e.lean}} : ${tag} a = ${tag} b ↔ a = b := ⟨${n}_inj, fun e => by rw [e]⟩
instance : Inj ${e.lean} := ⟨by rintro _ _ _ _ _ rfl rfl; simp [${n}_iff], by rintro _ _ _ rfl; simp, by rintro _ _ _ rfl; rfl⟩
theorem ${n}_eq {p s x y} {a b : ${e.lean}} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .eq x y) (a = b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary, ${n}_iff])
theorem ${n}_ne {p s x y} {a b : ${e.lean}} (hx : SimE p s x a) (hy : SimE p s y b) : SimC p s (.bin .ne x y) (a ≠ b) :=
  sim_cmp hx hy (by rintro _ _ _ rfl rfl; simp [binary, ${n}_iff])
macro_rules | \`(tactic| simc) => \`(tactic| (apply ${n}_eq; sim'; sim'))
macro_rules | \`(tactic| simc) => \`(tactic| (apply ${n}_ne; sim'; sim'))
${e.tags.map(t => `theorem ${n}_lit_${short(t.tag)} {p s} : SimE p s (.lit (.str ${units(t.tag)})) ${e.lean}.${t.lean} := fun s₁ _ => ⟨_, s₁, Evals.lit _ _ _, Ext.refl _, rfl⟩
macro_rules | \`(tactic| sim0) => \`(tactic| exact ${n}_lit_${short(t.tag)})`).join("\n")}`;
}

function recordRules(r, shapes) {
  const n = short(r.lean);
  const view = f => `(rep (α := ${leanType(f.type)}) h a.${f.lean} ((fs.lookup ${q(f.name)}).getD .undef))`;
  const pats = r.fields.map((_, i) => `f${i}`);
  const lines = [`instance : TyRep ${r.lean} where
  rep h a v := ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧ ${r.fields.map(view).join(" ∧ ")}
  mono hp := by
    rintro ⟨l, fs, rfl, hl, ${pats.join(", ")}⟩
    exact ⟨l, fs, rfl, lookup_mono hp hl, ${pats.map(p => `mono hp ${p}`).join(", ")}⟩
instance : IsObj ${r.lean} := ⟨fun ⟨l, _, h, _⟩ => ⟨l, h⟩⟩`];
  r.fields.forEach((f, i) => {
    const names = pats.map((p, j) => (j === i ? "hf" : "_")).join(", ");
    const open = `by rintro _ _ ⟨l, fs, rfl, hl, ${names}⟩; exact ⟨_, by simp [readField, hl], hf⟩`;
    lines.push(`theorem ${n}_get_${i} {p s o} {a : ${r.lean}} (h : SimE p s o a) : SimE (α := ${leanType(f.type)}) p s (.field o ${q(f.name)}) a.${f.lean} :=
  sim_field h (${open})
macro_rules | \`(tactic| sim0) => \`(tactic| (apply ${n}_get_${i}; sim'))
macro_rules | \`(tactic| sim_read) => \`(tactic| (apply ${n}_get_${i}; sim_read))
theorem ${n}_opt_${i} {p s o} {a : ${r.lean}} (h : SimE p s o a) : SimE (α := ${leanType(f.type)}) p s (.optField o ${q(f.name)}) a.${f.lean} :=
  sim_optField h (${open})
macro_rules | \`(tactic| sim0) => \`(tactic| (apply ${n}_opt_${i}; sim'))`);
  });
  // A literal, for each set of keys that the function writes.
  shapes.forEach((keys, si) => {
    const known = new Map(r.fields.map(f => [f.name, f]));
    if (!keys.every(k => known.has(k))) return;
    if (r.fields.some(f => !keys.includes(f.name) && f.type.kind !== "optional")) return;
    const args = keys.map((_, i) => `x${i}`), es = keys.map((_, i) => `e${i}`);
    const typed = keys.map((k, i) => `{x${i} : ${plain(known.get(k).type)}}`).join(" ");
    const hyps = keys.map((k, i) => `(h${i} : SimE (α := ${leanType(known.get(k).type)}) p s e${i} x${i})`).join(" ");
    const value = `{ ${r.fields.map(f => keys.includes(f.name) ? `${f.lean} := x${keys.indexOf(f.name)}` : `${f.lean} := none`).join(", ")} }`;
    const chain = keys.reduceRight((rest, _, i) => `simf_cons h${i} (${rest})`, "simf_nil");
    const destruct = keys.map((_, i) => `v${i}, _, rfl, r${i}`).join(", ");
    const fields = r.fields.map(f => {
      const i = keys.indexOf(f.name);
      return i < 0 ? `(by simp [List.lookup]; exact rfl)` : `(by simp [List.lookup]; exact mono (List.prefix_append _ _) r${i})`;
    });
    lines.push(`theorem ${n}_lit_${si} {p s ${es.join(" ")}} ${typed} ${hyps} :
    SimE p s (.record [${keys.map((k, i) => `(${q(k)}, e${i})`).join(", ")}]) (${value} : ${r.lean}) :=
  sim_record (${chain}) (by
    rintro _ _ ⟨${destruct}, rfl⟩
    exact ⟨_, [${keys.map((k, i) => `(${q(k)}, v${i})`).join(", ")}], rfl, by simp, ${fields.join(", ")}⟩)
macro_rules | \`(tactic| sim0) => \`(tactic| (apply ${n}_lit_${si} <;> sim))`);
  });
  return lines.join("\n");
}

export function generate(root, target, paths) {
  const { names: coreNames, callees, lean, sources } = lower(root, [target], { paths });
  const targets = sources.map(s => `${s.file}::${s.name}`);
  const view = translate({ root, module: "V", paths, targets });
  for (const t of targets) if (view.failures[t]) throw new Error(`callee rejected: ${view.failures[t]}`);
  const types = new Map();
  const scan = t => {
    if (t.kind === "record" || t.kind === "enum") { if (types.has(t.lean)) return; if (t.kind === "record") t.fields.forEach(f => scan(f.type)); types.set(t.lean, t); }
    if (t.kind === "optional") scan(t.inner);
    if (t.kind === "array") scan(t.item);
  };
  const sigs = sources.map(s => ({ ...s, sig: view.signatures[`${s.file}::${s.name}`] }));
  for (const { sig } of sigs) { sig.params.forEach(scan); scan(sig.result); }
  const shapes = recordShapes(lean);
  const rules = [...types.values()].map(t => t.kind === "enum" ? enumRules(t) : recordRules(t, shapes));
  const source = view.source.replace(/^import.*\n/gm, "").replace(/^open Aeneas.*\n/m, "");
  const constants = [...source.matchAll(/^def (\S+) : Result /gm)].map(m => m[1]);
  // Callees first: the view lists a function after what it calls.
  const position = s => source.indexOf(`def ${s.sig.lean} `);
  const ordered = [...sigs].sort((a, b) => position(a) - position(b));
  const theorems = ordered.map(({ key, sig }) => {
    const P = sig.params.map((_, i) => `p${i}`), Vs = sig.params.map((_, i) => `v${i}`);
    const typed = sig.params.map((t, i) => `{p${i} : ${plain(t)}}`).join(" ");
    const reps = sig.params.map((t, i) => `(h${i} : rep (α := ${leanType(t)}) h p${i} v${i})`).join(" ");
    const res = plain(sig.result), repRes = leanType(sig.result);
    const head = `theorem ${key}_bridge {h ${Vs.join(" ")}} ${typed} {r : ${res}} ${reps}
    (hr : ${sig.lean} ${P.join(" ")} = ok r) :
    WpRun prog ${key} [${Vs.join(", ")}] h fun v s => h <+: s.heap ∧ rep (α := ${repRes}) s.heap r v := by
  unfold ${sig.lean} at hr
${constants.map(c => `  try unfold ${c} at hr`).join("\n")}
  apply wprun'
  have hb : Base h ⟨${key}.env0 [${Vs.join(", ")}], h⟩ := List.prefix_refl _
${sig.params.map((t, i) => `  have hv${i} : V ⟨${key}.env0 [${Vs.join(", ")}], h⟩ ${q("PARAM" + i)} (α := ${leanType(t)}) p${i} := ⟨v${i}, by simp [${key}, Fn.env0, Env.put], h${i}⟩`).join("\n")}
  generalize St.mk (${key}.env0 [${Vs.join(", ")}]) h = s0 at *
  have hk : Todo _ _ := hr
  clear hr
  crun`;
    const n = sig.params.length;
    const args = sig.params.map((t, i) => `(h${i} : SimE (α := ${leanType(t)}) prog s e${i} p${i})`).join(" ");
    const call = n > 3 ? "" : `
theorem ${key}_sim {s ${P.length ? sig.params.map((_, i) => `e${i}`).join(" ") : ""}} ${typed} {r : ${res}} ${args}
    (hr : ${sig.lean} ${P.join(" ")} = ok r) : SimE (α := ${repRes}) prog s (.call ${q(key)} [${sig.params.map((_, i) => `e${i}`).join(", ")}]) r :=
  sim_call (fn := ${key}) (by simp [prog]) (${n === 0 ? "args0" : `args${n} ${sig.params.map((_, i) => `h${i}`).join(" ")}`}) (by
    rintro _ _ ${n === 0 ? "rfl" : `⟨${Vs.join(", ")}, rfl, ${sig.params.map((_, i) => `r${i}`).join(", ")}⟩`}
    exact ${key}_bridge ${sig.params.map((_, i) => `r${i}`).join(" ")} hr)
macro_rules | \`(tactic| sim0) => \`(tactic| (apply ${key}_sim; ${sig.params.map(() => "sim';").join(" ")} assumption))
macro_rules | \`(tactic| sim_read) => \`(tactic| (apply ${key}_sim; ${sig.params.map(() => "sim';").join(" ")} assumption))`;
    const params = JSON.parse(`[${lean.slice(lean.indexOf(`def ${key} : Fn`)).match(/params := \[(.*?)\]/)[1]}]`);
    return head.replaceAll(/"PARAM(\d+)"/g, (_, i) => q(params[i])) + call;
  });
  const core = lean.replace(/^import Core\nopen Core\n/, "").replace(/^namespace Gen\n/m, "").replace(/^end Gen\n/m, "");
  return { keys: coreNames, text: `import Spike.Tac
open Aeneas Aeneas.Std Result Core Core.TyRep
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

${source}
${core}
${rules.join("\n\n")}

${theorems.join("\n\n")}
${ordered.map(o => `#print axioms ${o.key}_bridge`).join("\n")}
` };
}

if (process.argv[1]?.endsWith("bridge3.mjs")) {
  const [list, outDir, filter] = process.argv.slice(2);
  const { readFileSync } = await import("node:fs");
  mkdirSync(outDir, { recursive: true });
  const rows = readFileSync(list, "utf8").trim().split("\n").map(l => l.split("\t"));
  const index = [];
  rows.forEach(([repo, file, fn], i) => {
    if (filter && !`${repo}/${file}::${fn}`.includes(filter)) return;
    const root = `${process.env.CORPUS ?? "/tmp/ts-corpus"}/${repo}`;
    try {
      const { text } = generate(root, `${file}::${fn}`, workspacePaths(root));
      writeFileSync(join(outDir, `F${i}.lean`), text);
      index.push({ i, repo, file, fn, ok: true });
    } catch (error) {
      index.push({ i, repo, file, fn, ok: false, reason: error.message.slice(0, 120) });
    }
  });
  writeFileSync(join(outDir, "index.json"), JSON.stringify(index, null, 0));
  const failed = index.filter(x => !x.ok);
  console.log(`${index.length - failed.length} generated, ${failed.length} failed`);
  const reasons = {};
  for (const f of failed) { const r = f.reason.replace(/`[^`]*`/g, "`_`").slice(0, 60); reasons[r] = (reasons[r] ?? 0) + 1; }
  console.log(Object.entries(reasons).sort((a, b) => b[1] - a[1]).slice(0, 20).map(([k, v]) => `${v}  ${k}`).join("\n"));
}
