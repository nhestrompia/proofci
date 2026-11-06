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
    case "void": return "Unit";
    case "generic": return t.name;
    case "array": return `(List ${leanType(t.item)})`;
    case "optional": return `(Opt ${t.both ? ".both" : t.nothing === "null" ? ".null" : ".undef"} ${leanType(t.inner)})`;
    default: throw new Error(`no encoding for ${t.kind}`);
  }
}

// The same type without the encoding marker: what the typed view itself uses.
const generics = t => t.kind === "generic" ? [t.name] : t.kind === "array" ? generics(t.item) : t.kind === "optional" ? generics(t.inner) : [];
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

// Reads the loops of a typed function, in source order.
function splitTop(text, sep) {
  const parts = []; let depth = 0, at = 0;
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if ("([{".includes(c)) depth++; else if (")]}".includes(c)) depth--;
    else if (depth === 0 && text.startsWith(sep, i)) { parts.push(text.slice(at, i)); at = i + sep.length; i += sep.length - 1; }
  }
  parts.push(text.slice(at));
  return parts.map(p => p.trim());
}
const unparen = t => { t = t.trim(); while (t.startsWith("(") && t.endsWith(")")) { let d = 0, whole = true; for (let i = 0; i < t.length - 1; i++) { if (t[i] === "(") d++; if (t[i] === ")") d--; if (d === 0) { whole = false; break; } } if (!whole) break; t = t.slice(1, -1).trim(); } return t; };
const base = n => n.replace(/[«»]/g, "").replace(/_\d+$/, "");
const pathOf = (root, i, n) => n === 1 ? root : (i === n - 1 ? root + ".2".repeat(i) : root + ".2".repeat(i) + ".1");

function viewLoops(text) {
  const loops = [];
  const mark = "(Aeneas.Std.loop (fun (state : ";
  for (let at = text.indexOf(mark); at >= 0; at = text.indexOf(mark, at + 1)) {
    const lineStart = text.lastIndexOf("\n", at) + 1;
    const binder = text.slice(lineStart, at).match(/let (.+?) ← $/)?.[1] ?? "_";
    const tStart = at + mark.length, tEnd = text.indexOf(") => match state with | ", tStart);
    const type = text.slice(tStart, tEnd);
    const pStart = tEnd + ") => match state with | ".length, pEnd = text.indexOf(" => do", pStart);
    const pat = text.slice(pStart, pEnd);
    let depth = 0, close = at, str = false;
    for (let i = at; i < text.length; i++) {
      const c = text[i];
      if (str) { if (c === '"') str = false; continue; }
      if (c === '"') str = true;
      else if (c === "(") depth++;
      else if (c === ")") { depth--; if (depth === 0) { close = i; break; } }
    }
    const inner = text.slice(at, close);
    const rs = inner.lastIndexOf(" : Result ");
    const result = unparen(inner.slice(rs + 10));
    const inr = text.slice(close).match(/\| \.inr (.+?) =>/)?.[1];
    loops.push({ binder, type, pat, result, inr });
  }
  return loops;
}

function loopRules(l, meta, retType, tv) {
  const K = meta.name;
  const parts = splitTop(unparen(l.pat), ",");
  const types = splitTop(l.type, "×");
  const isFor = meta.kind === "for";
  const list = isFor ? parts[0] : null;
  const vars = isFor ? parts.slice(1) : parts, tys = isFor ? types.slice(1) : types;
  const T = isFor ? unparen(types[0]).replace(/^List /, "") : null;
  const sigma = tys.length ? tys.join(" × ") : "Unit";
  const conj = (root, names, ts, s) => names.length ? names.map((n, i) => `V (α := ${ts[i]}) ${s} ${q(base(n))} ${pathOf(root, i, names.length)}`).join(" ∧ ") : "True";
  const isSum = l.result.startsWith("Sum ");
  const sum = isSum ? splitTop(l.result.slice(4), " ") : null;
  const carried = isSum ? (l.inr && l.inr !== "_" ? splitTop(unparen(l.inr), ",") : []) : (l.binder === "_" || /^tmp\d+$/.test(l.binder) ? [] : splitTop(unparen(l.binder), ","));
  const carriedTy = isSum ? (sum[1] === "(Unit)" || sum[1] === "Unit" ? [] : splitTop(unparen(sum[1]), "×")) : (carried.length ? splitTop(l.result, "×") : []);
  const beta = isSum ? `Sum ${sum[0]} ${sum[1]}` : l.result;
  const W = `[${meta.W.map(q).join(", ")}]`;
  const pattern = n => n === 0 ? "_" : n === 1 ? "a1" : `⟨${Array.from({ length: n }, (_, i) => `a${i + 1}`).join(", ")}⟩`;
  const rPat = n => n === 0 ? "_" : n === 1 ? "b1" : `⟨${Array.from({ length: n }, (_, i) => `b${i + 1}`).join(", ")}⟩`;
  const zb = isSum
    ? `match r with\n  | .inr y => ${conj("y", carried, carriedTy, "s")}\n  | .inl _ => False`
    : conj("r", carried, carriedTy, "s");
  const zr = isSum ? `match r with\n  | .inl a => rep (α := ${retType ?? unparen(sum[0])}) s.heap a v\n  | .inr _ => False` : "False";
  const mk = !isFor ? "" : vars.length ? "(fun l a => (l, a))" : "(fun l _ => l)";
  const defs = `def ${K}_R ${tv} (st : ${sigma}) (s : St) : Prop := ${conj("st", vars, tys, "s")}
def ${K}_Zb ${tv} (r : ${beta}) (s : St) : Prop := ${zb}
def ${K}_Zr ${tv} (r : ${beta}) (v : Val) (s : St) : Prop := ${zr}`;
  const a0 = vars.length ? "" : " (a0 := ())";
  const after = isSum
    ? `rcases res with b1 | ${rPat(carried.length)}`
    : "skip";
  const kr = isSum ? `(rcases res with b1 | _); (focus (dsimp only [${K}_Zr] at hz; have hk' := hk; unfold Todo at hk'; dsimp only at hk'; vsplit hk'; apply post_use hz hpre; post; assumption)); (focus (exact False.elim hz))` : "exact False.elim hz";
  const tail = `
  (focus (intro s5 hf hz; ${isSum ? `(rcases res with b1 | ${rPat(carried.length)}); exact False.elim hz; dsimp only [${K}_Zb] at hz; (try casesm* _ ∧ _); carry hf; clear hf; (try (unfold Todo at hk; simp only at hk; have hk3 : Todo _ _ := hk; clear hk)); crun` : `${after}; dsimp only [${K}_Zb] at hz; (try casesm* _ ∧ _); carry hf; clear hf; crun`}))
  (focus (intro v s6 hpre hz; ${kr}))))`;
  if (!isFor) return `${defs}
macro_rules | \`(tactic| c_while) => \`(tactic| (
  v_keep; intro res hl hk
  apply step_while (R := ${K}_R) (Zb := ${K}_Zb) (Zr := ${K}_Zr) (W := ${W}) hl
  (focus (l_conj))
  (focus (intro st s3 y hf hR hb; ${vars.length ? `rcases st with ${pattern(vars.length)}` : "skip"}; dsimp only [${K}_R] at hR; (try casesm* _ ∧ _); clear_todo; carry hf; clear hf; have hfr : Fr s3 s3 ${W} := Fr.refl _ _; have hb0 : Base s3.heap s3 := List.prefix_refl _; dsimp only at hb; have hk2 : Todo _ _ := hb; clear hb; crun))${tail}`;
  return `${defs}
macro_rules | \`(tactic| c_for) => \`(tactic| (
  v_keep; intro res hl hk
  apply step_for (mk := ${mk}) (R := ${K}_R) (Zb := ${K}_Zb) (Zr := ${K}_Zr) (W := ${W})${a0} hl
  sim
  (focus (intro s2 he; carry he; clear he; l_conj))
  (focus (intro ${pattern(vars.length)} s3 y hf hR hb; dsimp only [${K}_R] at hR; (try casesm* _ ∧ _); dsimp only at hb; vsplit hb; all_goals (refine ⟨_, rfl, ?_⟩; dsimp only [${K}_Zb]; l_conj)))
  (focus (intro q rest ${pattern(vars.length) === "_" ? "_" : "st"} s3 w y hf hR hw hb; ${vars.length ? `rcases st with ${pattern(vars.length)}` : "skip"}; dsimp only [${K}_R] at hR; (try casesm* _ ∧ _); clear_todo; carry hf; clear hf; apply enter; intro s4 hu he2 hh; have hvq := V.mk' (α := ${T}) he2 hh hw; have hb0 := base_of hh; have hfr : Fr s3 s4 ${W} := Fr.upd (Fr.refl _ _) hu (by decide); carry hu; clear hu he2 hh; dsimp only at hb; have hk2 : Todo _ _ := hb; clear hb; crun))${tail}`;
}

function enumRules(e) {
  const n = short(e.lean);
  const tag = `${n}_tag`;
  return `def ${tag} : ${e.lean} → List Nat
${e.tags.map(t => `  | .${t.lean} => ${units(t.tag)}`).join("\n")}
instance : TyRep ${e.lean} := ⟨fun _ a v => v = .str (${tag} a), fun _ h => h⟩
instance : NotNull ${e.lean} := ⟨by rintro _ _ _ rfl; rfl⟩
instance : AlwaysTruthy ${e.lean} := ⟨by rintro _ a _ rfl; cases a <;> rfl⟩
instance : Shown ${e.lean} := ⟨${e.lean}.toJsStr, by rintro _ a _ rfl; cases a <;> rfl⟩
theorem ${n}_text {p s x} {a : ${e.lean}} (hx : SimE p s x a) : SimE p s (.prim .toText [x]) (${e.lean}.toJsStr a) := SimE.toText hx
macro_rules | \`(tactic| s_prim) => \`(tactic| (apply ${n}_text; sim'))
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
macro_rules | \`(tactic| s_lit) => \`(tactic| exact ${n}_lit_${short(t.tag)})`).join("\n")}`;
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
macro_rules | \`(tactic| s_field) => \`(tactic| (apply ${n}_get_${i}; sim'))
macro_rules | \`(tactic| sim_read) => \`(tactic| (apply ${n}_get_${i}; sim_read))
theorem ${n}_opt_${i} {p s o} {a : ${r.lean}} (h : SimE p s o a) : SimE (α := ${leanType(f.type)}) p s (.optField o ${q(f.name)}) a.${f.lean} :=
  sim_optField h (${open})
macro_rules | \`(tactic| s_field) => \`(tactic| (apply ${n}_opt_${i}; sim'))`);
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
macro_rules | \`(tactic| s_rec) => \`(tactic| (apply ${n}_lit_${si} <;> sim))`);
  });
  return lines.join("\n");
}

export function generate(root, target, paths) {
  const { names: coreNames, lean, sources, loops: loopMeta } = lower(root, [target], { paths });
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
  const cbNames = [...lean.matchAll(/^def (\S+_cb\d+) : Fn/gm)].map(m => m[1]);
  const cbRules = cbNames.map(n => `theorem ${n}_prog : prog ${q(n)} = some ${n} := by simp [prog]
macro_rules | \`(tactic| prog_lookup) => \`(tactic| exact ${n}_prog)`).join("\n");
  const theorems = ordered.map(({ key, sig }) => {
    const defAt = source.indexOf(`def ${sig.lean} `);
    const defText = source.slice(defAt, source.indexOf("\n\n", defAt) < 0 ? undefined : source.indexOf("\n\n", defAt));
    const vl = viewLoops(defText), ml = loopMeta.filter(l => l.key === key).sort((a, b) => a.idx - b.idx);
    if (vl.length !== ml.length) throw new Error(`loops don't line up: ${vl.length} in the view, ${ml.length} in Core`);
    const tvars0 = [...new Set([...sig.params, sig.result].flatMap(generics))];
    const tv0 = tvars0.map(g => `{${g} : Type} [TyRep ${g}]`).join(" ");
    const loopText = vl.map((l, i) => loopRules(l, ml[i], leanType(sig.result), tv0)).join("\n");
    const P = sig.params.map((_, i) => `p${i}`), Vs = sig.params.map((_, i) => `v${i}`);
    const typed = sig.params.map((t, i) => `{p${i} : ${plain(t)}}`).join(" ");
    const reps = sig.params.map((t, i) => `(h${i} : rep (α := ${leanType(t)}) h p${i} v${i})`).join(" ");
    const res = plain(sig.result), repRes = leanType(sig.result);
    const tvars = [...new Set([...sig.params, sig.result].flatMap(generics))];
    const tv = tvars.map(g => `{${g} : Type} [DecidableEq ${g}] [TyRep ${g}]`).join(" ");
    const head = `theorem ${key}_bridge ${tv} {h ${Vs.join(" ")}} ${typed} {r : ${res}} ${reps}
    (hr : ${sig.lean} ${P.join(" ")} = ok r) :
    WpRun prog ${key} [${Vs.join(", ")}] h fun v s => h <+: s.heap ∧ rep (α := ${repRes}) s.heap r v := by
  unfold ${sig.lean} at hr
${[...constants].reverse().map(c => `  try unfold ${c} at hr`).join("\n")}
  apply ${sig.result.kind === "void" ? "wprun_unit" : "wprun'"}
  have hb : Base h ⟨${key}.env0 [${Vs.join(", ")}], h⟩ := List.prefix_refl _
${sig.params.map((t, i) => `  have hv${i} : V ⟨${key}.env0 [${Vs.join(", ")}], h⟩ ${q("PARAM" + i)} (α := ${leanType(t)}) p${i} := ⟨v${i}, by simp [${key}, Fn.env0, Env.put], h${i}⟩`).join("\n")}
  generalize St.mk (${key}.env0 [${Vs.join(", ")}]) h = s0 at *
  have hk : Todo _ _ := hr
  clear hr
  crun`;
    const n = sig.params.length;
    const args = sig.params.map((t, i) => `(h${i} : SimE (α := ${leanType(t)}) prog s e${i} p${i})`).join(" ");
    const call = n > 3 ? "" : `
theorem ${key}_sim ${tv} {s ${P.length ? sig.params.map((_, i) => `e${i}`).join(" ") : ""}} ${typed} {r : ${res}} ${args}
    (hr : ${sig.lean} ${P.join(" ")} = ok r) : SimE (α := ${repRes}) prog s (.call ${q(key)} [${sig.params.map((_, i) => `e${i}`).join(", ")}]) r :=
  sim_call (fn := ${key}) (by simp [prog]) (${n === 0 ? "args0" : `args${n} ${sig.params.map((_, i) => `h${i}`).join(" ")}`}) (by
    rintro _ _ ${n === 0 ? "rfl" : `⟨${Vs.join(", ")}, rfl, ${sig.params.map((_, i) => `r${i}`).join(", ")}⟩`}
    exact ${key}_bridge ${sig.params.map((_, i) => `r${i}`).join(" ")} hr)
macro_rules | \`(tactic| s_call) => \`(tactic| (apply ${key}_sim; ${sig.params.map(() => "sim';").join(" ")} assumption))
macro_rules | \`(tactic| sim_read) => \`(tactic| (apply ${key}_sim; ${sig.params.map(() => "sim';").join(" ")} assumption))`;
    const params = JSON.parse(`[${lean.slice(lean.indexOf(`def ${key} : Fn`)).match(/params := \[(.*?)\]/)[1]}]`);
    return (loopText ? loopText + "\n" : "") + head.replaceAll(/"PARAM(\d+)"/g, (_, i) => q(params[i])) + call;
  });
  const core = lean.replace(/^import Core\nopen Core\n/, "").replace(/^namespace Gen\n/m, "").replace(/^end Gen\n/m, "");
  return { keys: coreNames, text: `import Spike.Tac
open Aeneas Aeneas.Std Result Core Core.TyRep
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

${source}
${core}
${rules.join("\n\n")}

${cbRules}

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
