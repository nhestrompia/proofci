// Writes one Lean file per function: its typed view, its Core, and a bridge theorem proved
// by the shared tactics. Nothing here depends on which function it is given.
import { mkdirSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { lower } from "./lower.mjs";
import { translate } from "../../typescript/translate.mjs";
import { workspacePaths } from "../../typescript/paths.mjs";

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
    case "record": return t.args ? `(${t.lean} ${t.args.map(leanType).join(" ")})` : t.lean;
    case "enum": return t.lean;
    case "void": return "Unit";
    case "generic": return t.name;
    case "recursive": return t.lean;
    case "tagged": return t.args ? `(${t.lean} ${t.args.map(leanType).join(" ")})` : t.lean;
    case "array": case "set": return `(List ${leanType(t.item)})`;
    case "dict": return `(Js.Dict Js.Str ${leanType(t.value)})`;
    case "optional": return `(Opt ${t.both ? ".both" : t.nothing === "null" ? ".null" : ".undef"} ${leanType(t.inner)})`;
    default: throw new Error(`no encoding for ${t.kind}`);
  }
}

// The same type without the encoding marker: what the typed view itself uses.
const generics = t => t.kind === "generic" ? [t] : t.kind === "array" ? generics(t.item) : t.kind === "optional" ? generics(t.inner)
  : (t.kind === "record" || t.kind === "tagged") && t.args ? t.args.flatMap(generics) : [];
// A type parameter that can't be `null` or `undefined` keeps `Option T` one-to-one, as `NotNull` says.
// A rule that tactics apply before its type parameter is known takes the instances as implicit
// arguments, which unification fills in later.
const binders = (ts, { eq = false, late = false } = {}) => [...new Map(ts.flatMap(generics).map(g => [g.name, g])).values()]
  .map(g => `{${g.name} : Type}${eq ? (late ? ` {_ : DecidableEq ${g.name}}` : ` [DecidableEq ${g.name}]`) : ""}${late ? ` {_ : TyRep ${g.name}}` : ` [TyRep ${g.name}]`}${g.nonNull ? ` [NotNull ${g.name}]` : ""}`).join(" ");
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

// A record that holds itself, through `T | null`, `T | undefined` or `T[]`. Its encoding can't be
// written with `rep` of its field types, which would need its own instance, so it is defined by
// structural recursion (with a helper for a list of it). `_rep_iff` gives it the shape of any other
// record's encoding, which the rules below then use.
function selfRules(record) {
  const n = short(record.lean), T = record.lean;
  const isSelf = t => t.kind === "recursive" && t.lean === T;
  const kindOf = t => (t.both ? ".both" : t.nothing === "null" ? ".null" : ".undef");
  const form = t => isSelf(t) ? "self" : t.kind === "optional" && isSelf(t.inner) ? "opt" : t.kind === "array" && isSelf(t.item) ? "list" : null;
  const mentions = t => JSON.stringify(t).includes(`"kind":"recursive","lean":${q(T)}`);
  record.fields.forEach(f => {
    if (form(f.type) === "self" || (!form(f.type) && mentions(f.type))) throw new Error(`no encoding for recursive \`${f.name}\``);
  });
  const lists = record.fields.some(f => form(f.type) === "list");
  const fv = record.fields.map((_, i) => `f${i}`);
  const at = f => `((fs.lookup ${q(f.name)}).getD .undef)`;
  const body = (f, i) => form(f.type) === "opt"
    ? `(match f${i} with | none => nothingOk ${kindOf(f.type)} ${at(f)} | some x => ${n}_rep h x ${at(f)})`
    : form(f.type) === "list"
      ? `(∃ l' vs, ${at(f)} = .ref l' ∧ h[l']? = some (.array vs) ∧ ${n}_reps h f${i} vs)`
      : `rep (α := ${leanType(f.type)}) h f${i} ${at(f)}`;
  const mono = (f, i) => form(f.type) === "opt"
    ? `(by match f${i}, r${i} with | none, r => exact r | some x, r => exact ${n}_rep_mono hp x _ r)`
    : form(f.type) === "list"
      ? `(by obtain ⟨l', vs, e, hl', rs⟩ := r${i}; exact ⟨l', vs, e, lookup_mono hp hl', ${n}_reps_mono hp _ _ rs⟩)`
      : `mono hp r${i}`;
  const view = f => `(rep (α := ${leanType(f.type)}) h a.${f.lean} ${at(f)})`;
  const rs = record.fields.map((_, i) => `r${i}`).join(", ");
  const opts = record.fields.map((f, i) => form(f.type) === "opt" ? `cases f${i}` : null).filter(Boolean);
  return `mutual
def ${n}_rep (h : Heap) : ${T} → Val → Prop
  | ⟨${fv.join(", ")}⟩, v => ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧ ${record.fields.map(body).join(" ∧ ")}${lists ? `
def ${n}_reps (h : Heap) : List ${T} → List Val → Prop
  | [], [] => True
  | x :: xs, v :: vs => ${n}_rep h x v ∧ ${n}_reps h xs vs
  | _, _ => False` : ""}
end
mutual
theorem ${n}_rep_mono {h h' : Heap} (hp : h <+: h') : ∀ (a : ${T}) (v : Val), ${n}_rep h a v → ${n}_rep h' a v
  | ⟨${fv.join(", ")}⟩, v, hr => by
    unfold ${n}_rep at hr ⊢
    obtain ⟨l, fs, rfl, hl, ${rs}⟩ := hr
    exact ⟨l, fs, rfl, lookup_mono hp hl, ${record.fields.map(mono).join(", ")}⟩${lists ? `
theorem ${n}_reps_mono {h h' : Heap} (hp : h <+: h') : ∀ (xs : List ${T}) (vs : List Val), ${n}_reps h xs vs → ${n}_reps h' xs vs
  | [], [], hr => hr
  | x :: xs, v :: vs, hr => by
    unfold ${n}_reps at hr ⊢
    exact ⟨${n}_rep_mono hp x v hr.1, ${n}_reps_mono hp xs vs hr.2⟩
  | [], _ :: _, hr => hr
  | _ :: _, [], hr => hr` : ""}
end
instance : TyRep ${T} := ⟨${n}_rep, fun hp r => ${n}_rep_mono hp _ _ r⟩${lists ? `
theorem ${n}_reps_iff {h : Heap} : ∀ (xs : List ${T}) (vs : List Val), ${n}_reps h xs vs ↔ List.Forall₂ (rep (α := ${T}) h) xs vs
  | [], [] => by simp [${n}_reps]
  | x :: xs, v :: vs => by simp only [${n}_reps, List.forall₂_cons, ${n}_reps_iff xs vs]; exact Iff.rfl
  | [], _ :: _ => by simp [${n}_reps]
  | _ :: _, [] => by simp [${n}_reps]` : ""}
theorem ${n}_rep_iff {h : Heap} {a : ${T}} {v : Val} :
    rep h a v ↔ ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧ ${record.fields.map(view).join(" ∧ ")} := by
  obtain ⟨${fv.join(", ")}⟩ := a
  ${opts.length ? `(${opts.join(" <;> ")}) <;> ` : ""}(show ${n}_rep h _ v ↔ _; unfold ${n}_rep; ${lists ? `simp only [${n}_reps_iff]; ` : ""}exact Iff.rfl)`;
}

// A union tagged by `kind`: an object whose `kind` is its variant's tag, with that variant's fields.
// It may hold itself directly (another variant ends it), or through `T | null`, `T | undefined` or `T[]`.
function taggedRules(given, shapes) {
  const n = short(given.lean), tag = `${n}_tag`;
  const u = given.params ? { ...given, variants: given.declared, lean: `(${given.lean} ${given.params.join(" ")})` } : given;
  const T = u.lean;
  const isSelf = t => t.kind === "recursive" && t.lean === T;
  const kindOf = t => (t.both ? ".both" : t.nothing === "null" ? ".null" : ".undef");
  const form = t => isSelf(t) ? "self" : t.kind === "optional" && isSelf(t.inner) ? "opt" : t.kind === "array" && isSelf(t.item) ? "list" : null;
  const mentions = t => JSON.stringify(t).includes(`"kind":"recursive","lean":${q(T)}`);
  const all = u.variants.flatMap(v => v.fields);
  all.forEach(f => { if (!form(f.type) && mentions(f.type)) throw new Error(`no encoding for recursive \`${f.name}\``); });
  const lists = all.some(f => form(f.type) === "list");
  const at = f => `((fs.lookup ${q(f.name)}).getD .undef)`;
  const body = (f, i) => form(f.type) === "self" ? `${n}_rep h f${i} ${at(f)}` : form(f.type) === "opt"
    ? `(match f${i} with | none => nothingOk ${kindOf(f.type)} ${at(f)} | some x => ${n}_rep h x ${at(f)})`
    : form(f.type) === "list"
      ? `(∃ l' vs, ${at(f)} = .ref l' ∧ h[l']? = some (.array vs) ∧ ${n}_reps h f${i} vs)`
      : `rep (α := ${leanType(f.type)}) h f${i} ${at(f)}`;
  const mono = (f, i) => form(f.type) === "self" ? `${n}_rep_mono hp f${i} _ r${i}` : form(f.type) === "opt"
    ? `(by match f${i}, r${i} with | none, r => exact r | some x, r => exact ${n}_rep_mono hp x _ r)`
    : form(f.type) === "list"
      ? `(by obtain ⟨l', vs, e, hl', rs⟩ := r${i}; exact ⟨l', vs, e, lookup_mono hp hl', ${n}_reps_mono hp _ _ rs⟩)`
      : `mono hp r${i}`;
  const conv = (f, i) => form(f.type) === "opt" ? `(by cases f${i} <;> exact r${i})`
    : form(f.type) === "list" ? `(by obtain ⟨l', vs, e, hl', rs⟩ := r${i}; exact ⟨l', vs, e, hl', (${n}_reps_iff _ _).mp rs⟩)`
    : `r${i}`;
  const fv = v => v.fields.map((_, i) => `f${i}`);
  const pat = v => `.${v.lean}${fv(v).map(f => ` ${f}`).join("")}`;
  const rs = v => ["hk", ...v.fields.map((_, i) => `r${i}`)].join(", ");
  const kind = v => `((fs.lookup "kind").getD .undef) = .str ${units(v.tag)}`;
  const open = `change ${n}_rep _ _ _ at hr; unfold ${n}_rep at hr`;
  const lines = [`@[simp] def ${tag} : ${T} → List Nat
${u.variants.map(v => `  | .${v.lean}${v.fields.map(() => " _").join("")} => ${units(v.tag)}`).join("\n")}
${lists ? "mutual\n" : ""}def ${n}_rep (h : Heap) : ${T} → Val → Prop
${u.variants.map(v => `  | ${pat(v)}, v => ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧ ${[kind(v), ...v.fields.map(body)].join(" ∧ ")}`).join("\n")}${lists ? `
def ${n}_reps (h : Heap) : List ${T} → List Val → Prop
  | [], [] => True
  | x :: xs, v :: vs => ${n}_rep h x v ∧ ${n}_reps h xs vs
  | _, _ => False
end
mutual` : ""}
theorem ${n}_rep_mono {h h' : Heap} (hp : h <+: h') : ∀ (a : ${T}) (v : Val), ${n}_rep h a v → ${n}_rep h' a v
${u.variants.map(v => `  | ${pat(v)}, v, hr => by
    unfold ${n}_rep at hr ⊢
    obtain ⟨l, fs, rfl, hl, ${rs(v)}⟩ := hr
    exact ⟨l, fs, rfl, lookup_mono hp hl, ${["hk", ...v.fields.map(mono)].join(", ")}⟩`).join("\n")}${lists ? `
theorem ${n}_reps_mono {h h' : Heap} (hp : h <+: h') : ∀ (xs : List ${T}) (vs : List Val), ${n}_reps h xs vs → ${n}_reps h' xs vs
  | [], [], hr => hr
  | x :: xs, v :: vs, hr => by
    unfold ${n}_reps at hr ⊢
    exact ⟨${n}_rep_mono hp x v hr.1, ${n}_reps_mono hp xs vs hr.2⟩
  | [], _ :: _, hr => hr
  | _ :: _, [], hr => hr
end` : ""}
instance : TyRep ${T} := ⟨${n}_rep, fun hp r => ${n}_rep_mono hp _ _ r⟩${lists ? `
theorem ${n}_reps_iff {h : Heap} : ∀ (xs : List ${T}) (vs : List Val), ${n}_reps h xs vs ↔ List.Forall₂ (rep (α := ${T}) h) xs vs
  | [], [] => by simp [${n}_reps]
  | x :: xs, v :: vs => by simp only [${n}_reps, List.forall₂_cons, ${n}_reps_iff xs vs]; exact Iff.rfl
  | [], _ :: _ => by simp [${n}_reps]
  | _ :: _, [] => by simp [${n}_reps]` : ""}
instance : IsObj ${T} := ⟨fun {_ a _} hr => by
  cases a <;> (${open}; obtain ⟨l, _, he, _⟩ := hr; exact ⟨l, he⟩)⟩
theorem ${n}_kind {p s o} {a : ${T}} (h : SimE p s o a) : SimE (α := List Nat) p s (.field o "kind") (${tag} a) :=
  sim_field h (by
    intro _ _ hr
    cases a <;> (${open}; first
      | (obtain ⟨l, fs, rfl, hl, hk⟩ := hr; exact ⟨(fs.lookup "kind").getD .undef, by simp [readField, hl], hk⟩)
      | (obtain ⟨l, fs, rfl, hl, hk, -⟩ := hr; exact ⟨(fs.lookup "kind").getD .undef, by simp [readField, hl], hk⟩)))
macro_rules | \`(tactic| s_field) => \`(tactic| (apply ${n}_kind; sim'))
macro_rules | \`(tactic| sim_read) => \`(tactic| (apply ${n}_kind; sim_read))`];
  u.variants.forEach(v => v.fields.forEach((f, i) => {
    const name = `${n}_get_${short(v.lean)}_${i}`;
    lines.push(`theorem ${name} {p s o} ${fv(v).map((x, j) => `{${x} : ${plain(v.fields[j].type)}}`).join(" ")} (h : SimE p s o (${pat(v)} : ${T})) : SimE (α := ${leanType(f.type)}) p s (.field o ${q(f.name)}) f${i} :=
  sim_field h (by
    intro _ _ hr; ${open}
    obtain ⟨l, fs, rfl, hl, ${rs(v)}⟩ := hr
    exact ⟨${at(f)}, by simp [readField, hl], ${conv(f, i)}⟩)
macro_rules | \`(tactic| s_field) => \`(tactic| (apply ${name}; sim'))
macro_rules | \`(tactic| sim_read) => \`(tactic| (apply ${name}; sim_read))`);
    // Once the view has matched a nullable field as present, a read of it is the value inside.
    if (f.type.kind === "optional") lines.push(`macro_rules | \`(tactic| s_field) => \`(tactic| (apply SimE.unwrap; apply ${name}; sim'; rfl))`);
  }));
  // A literal of a variant, for each set of keys the function writes that is exactly that variant's.
  shapes.forEach((keys, si) => u.variants.forEach(v => {
    const names = ["kind", ...v.fields.map(f => f.name)];
    if (keys.length !== names.length || !names.every(k => keys.includes(k)) || v.fields.some(f => form(f.type))) return;
    const field = k => v.fields.find(f => f.name === k);
    const es = keys.map((k, i) => k === "kind" ? `(.lit (.str ${units(v.tag)}))` : `e${i}`);
    const hyps = keys.map((k, i) => k === "kind" ? "" : `(h${i} : SimE (α := ${leanType(field(k).type)}) p s e${i} x${i})`).join(" ");
    const typed = keys.map((k, i) => k === "kind" ? "" : `{e${i}} {x${i} : ${plain(field(k).type)}}`).join(" ");
    const chain = keys.reduceRight((rest, k, i) => `simf_cons ${k === "kind" ? `(SimE.lit_str ${units(v.tag)})` : `h${i}`} (${rest})`, "simf_nil");
    const destruct = keys.map((_, i) => `v${i}, _, rfl, r${i}`).join(", ");
    const parts = [`(by simp [List.lookup]; exact r${keys.indexOf("kind")})`,
      ...v.fields.map(f => `(by simp [List.lookup]; exact mono (List.prefix_append _ _) r${keys.indexOf(f.name)})`)];
    const value = `(.${v.lean}${v.fields.map(f => ` x${keys.indexOf(f.name)}`).join("")} : ${T})`;
    lines.push(`theorem ${n}_lit_${short(v.lean)}_${si} {p s} ${typed} ${hyps} :
    SimE p s (.record [${keys.map((k, i) => `(${q(k)}, ${es[i]})`).join(", ")}]) ${value} :=
  sim_record (${chain}) (by
    rintro _ _ ⟨${destruct}, rfl⟩
    show ${n}_rep _ _ _; unfold ${n}_rep
    exact ⟨_, [${keys.map((k, i) => `(${q(k)}, v${i})`).join(", ")}], rfl, by simp, ${parts.join(", ")}⟩)
macro_rules | \`(tactic| s_rec) => \`(tactic| (apply ${n}_lit_${short(v.lean)}_${si} <;> sim))`);
  }));
  if (!u.params) return lines.join("\n");
  // One set of rules for every use: each takes the type's parameters, with an encoding for each.
  // A theorem takes the encodings as implicit arguments, so `apply` finds them by unification.
  const binders = ` ${u.params.map(p => `{${p} : Type} [TyRep ${p}]`).join(" ")}`;
  const implicit = ` ${u.params.map(p => `{${p} : Type} {_ : TyRep ${p}}`).join(" ")}`;
  return lines.join("\n").replace(new RegExp(`^(@\\[simp\\] def|def) (${n}_\\w*)`, "gm"), `$1 $2${binders}`)
    .replace(new RegExp(`^theorem (${n}_\\w*)`, "gm"), `theorem $1${implicit}`)
    .replace(/^instance : /gm, `instance${binders} : `);
}

function recordRules(record, shapes) {
  const n = short(record.lean);
  const self = !record.params && JSON.stringify(record.fields).includes(`"kind":"recursive","lean":${q(record.lean)}`);
  const r = record.params ? { ...record, fields: record.declared, lean: `(${record.lean} ${record.params.join(" ")})` } : record;
  const instance = r.params ? r.params.map(p => `{${p} : Type} [TyRep ${p}]`).join(" ") : "";
  const tv = r.params ? r.params.map(p => `{${p} : Type} {_ : TyRep ${p}}`).join(" ") : "";
  const view = f => `(rep (α := ${leanType(f.type)}) h a.${f.lean} ((fs.lookup ${q(f.name)}).getD .undef))`;
  const pats = r.fields.map((_, i) => `f${i}`);
  const lines = [self ? `${selfRules(r)}
instance : IsObj ${r.lean} := ⟨fun hr => by obtain ⟨l, _, h, _⟩ := ${n}_rep_iff.mp hr; exact ⟨l, h⟩⟩` : `instance ${instance} : TyRep ${r.lean} where
  rep h a v := ∃ l fs, v = .ref l ∧ h[l]? = some (.record fs) ∧ ${r.fields.map(view).join(" ∧ ")}
  mono hp := by
    rintro ⟨l, fs, rfl, hl, ${pats.join(", ")}⟩
    exact ⟨l, fs, rfl, lookup_mono hp hl, ${pats.map(p => `mono hp ${p}`).join(", ")}⟩
instance ${instance} : IsObj ${r.lean} := ⟨fun ⟨l, _, h, _⟩ => ⟨l, h⟩⟩`];
  r.fields.forEach((f, i) => {
    const names = pats.map((p, j) => (j === i ? "hf" : "_")).join(", ");
    const open = self
      ? `by intro _ _ hr; obtain ⟨l, fs, rfl, hl, ${names}⟩ := ${n}_rep_iff.mp hr; exact ⟨_, by simp [readField, hl], hf⟩`
      : `by rintro _ _ ⟨l, fs, rfl, hl, ${names}⟩; exact ⟨_, by simp [readField, hl], hf⟩`;
    lines.push(`theorem ${n}_get_${i} ${tv} {p s o} {a : ${r.lean}} (h : SimE p s o a) : SimE (α := ${leanType(f.type)}) p s (.field o ${q(f.name)}) a.${f.lean} :=
  sim_field h (${open})
macro_rules | \`(tactic| s_field) => \`(tactic| (apply ${n}_get_${i}; sim'))
macro_rules | \`(tactic| sim_read) => \`(tactic| (apply ${n}_get_${i}; sim_read))
theorem ${n}_opt_${i} ${tv} {p s o} {a : ${r.lean}} (h : SimE p s o a) : SimE (α := ${leanType(f.type)}) p s (.optField o ${q(f.name)}) a.${f.lean} :=
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
    lines.push(`theorem ${n}_lit_${si} ${tv} {p s ${es.join(" ")}} ${typed} ${hyps} :
    SimE p s (.record [${keys.map((k, i) => `(${q(k)}, e${i})`).join(", ")}]) (${value} : ${r.lean}) :=
  sim_record (${chain}) (by
    rintro _ _ ⟨${destruct}, rfl⟩
    exact ${self ? `${n}_rep_iff.mpr ` : ""}⟨_, [${keys.map((k, i) => `(${q(k)}, v${i})`).join(", ")}], rfl, by simp, ${fields.join(", ")}⟩)
macro_rules | \`(tactic| s_rec) => \`(tactic| (apply ${n}_lit_${si} <;> sim))`);
  });
  return lines.join("\n");
}

// `viewSource` is the text of the typed view to prove about; without it the view is translated
// afresh. The action passes the module it extracted, so the bridge is about the very definitions a
// user's proof is about. `options` are the further settings the translator was given there.
export function generate(root, target, paths, { viewSource, options } = {}) {
  const { names: coreNames, lean, sources, loops: loopMeta } = lower(root, [target], { paths });
  const targets = sources.map(s => `${s.file}::${s.name}`);
  const view = translate({ root, module: "V", paths, targets, ...options });
  for (const t of targets) if (view.failures[t]) throw new Error(`callee rejected: ${view.failures[t]}`);
  const types = new Map();
  const scan = t => {
    if (t.kind === "record") t.args?.forEach(scan);
    if (t.kind === "record" || t.kind === "enum") { if (types.has(t.lean)) return; if (t.kind === "record") (t.declared ?? t.fields).forEach(f => scan(f.type)); types.set(t.lean, t); }
    if (t.kind === "tagged") t.args?.forEach(scan);
    if (t.kind === "tagged" && !types.has(t.lean)) { t.variants.forEach(v => v.fields.forEach(f => scan(f.type))); types.set(t.lean, t); }
    if (t.kind === "optional") scan(t.inner);
    if (t.kind === "array") scan(t.item);
    if (t.kind === "dict") scan(t.value);
  };
  const sigs = sources.map(s => ({ ...s, sig: view.signatures[`${s.file}::${s.name}`] }));
  for (const { sig } of sigs) { sig.params.forEach(scan); scan(sig.result); }
  // A record met only inside a constant or a callback, when every field has an encoding.
  const encodable = t => t.kind === "record" ? t.fields.every(f => encodable(f.type))
    : t.kind === "tagged" ? t.variants.every(v => v.fields.every(f => encodable(f.type)))
    : t.kind === "optional" ? encodable(t.inner)
    : t.kind === "array" || t.kind === "set" ? encodable(t.item)
    : t.kind === "dict" ? encodable(t.value)
    : t.kind !== "map";
  for (const t of view.records()) if (t.kind === "record" && encodable(t)) scan(t);
  const shapes = recordShapes(lean);
  const rules = [...types.values()].map(t => t.kind === "enum" ? enumRules(t) : t.kind === "tagged" ? taggedRules(t, shapes) : recordRules(t, shapes));
  const source = (viewSource ?? view.source).replace(/^import.*\n/gm, "").replace(/^open Aeneas.*\n/m, "");
  // Callees first: the view lists a function after what it calls.
  const position = s => source.indexOf(`def ${s.sig.lean} `);
  const ordered = [...sigs].sort((a, b) => position(a) - position(b));
  // Only the constants these functions use: a module that translates other functions too has more.
  const reachable = ordered.map(s => { const at = position(s); return at < 0 ? "" : source.slice(at, source.indexOf("\n\n", at) < 0 ? undefined : source.indexOf("\n\n", at)); }).join("\n");
  const constants = [...source.matchAll(/^def (\S+) : Result /gm)].map(m => m[1]).filter(c => reachable.includes(c));
  const cbNames = [...lean.matchAll(/^def (\S+_cb\d+) : Fn/gm)].map(m => m[1]);
  const cbRules = cbNames.map(n => `theorem ${n}_prog : prog ${q(n)} = some ${n} := by simp [prog]
macro_rules | \`(tactic| prog_lookup) => \`(tactic| exact ${n}_prog)`).join("\n");
  const mutualGroups = new Map();
  const theorems = ordered.map(({ key, sig }) => {
    const defAt = source.indexOf(`def ${sig.lean} `);
    if (defAt < 0) throw new Error(`the view has no definition of ${sig.lean}`);
    const defText = source.slice(defAt, source.indexOf("\n\n", defAt) < 0 ? undefined : source.indexOf("\n\n", defAt));
    const block = source.lastIndexOf("\nmutual\n", defAt);
    const blockEnd = block < 0 ? -1 : source.indexOf("\nend", block);
    let group;
    if (blockEnd > defAt) {
      const names = [...source.slice(block, blockEnd).matchAll(/^def (\S+) /gm)].map(m => m[1]);
      const members = ordered.filter(o => names.includes(o.sig.lean));
      if (members.length !== names.length) throw new Error("a mutually recursive function has a member with no signature to bridge");
      if (members.some(o => binders([...o.sig.params, o.sig.result]))) throw new Error("generic mutually recursive functions have no bridge yet");
      group = mutualGroups.get(block) ?? { size: names.length, parts: [] };
      mutualGroups.set(block, group);
    }
    const vl = viewLoops(defText), ml = loopMeta.filter(l => l.key === key).sort((a, b) => a.idx - b.idx);
    if (vl.length !== ml.length) throw new Error(`loops don't line up: ${vl.length} in the view, ${ml.length} in Core`);
    const tv0 = binders([...sig.params, sig.result]);
    const loopText = vl.map((l, i) => loopRules(l, ml[i], leanType(sig.result), tv0)).join("\n");
    const P = sig.params.map((_, i) => `p${i}`), Vs = sig.params.map((_, i) => `v${i}`);
    const typed = sig.params.map((t, i) => `{p${i} : ${plain(t)}}`).join(" ");
    const reps = sig.params.map((t, i) => `(h${i} : rep (α := ${leanType(t)}) h p${i} v${i})`).join(" ");
    const res = plain(sig.result), repRes = leanType(sig.result);
    const tv = binders([...sig.params, sig.result], { eq: true });
    const run = `WpRun prog ${key} [${Vs.join(", ")}] h fun v s => h <+: s.heap ∧ rep (α := ${repRes}) s.heap r v`;
    const n = sig.params.length;
    // A function that calls itself is proved by induction over its `partial_fixpoint`: each call it
    // makes to itself is the function the step is given, and the hypothesis bridges that call.
    const recursive = /\npartial_fixpoint\s*$/.test(defText);
    if (recursive && (n === 0 || n > 6)) throw new Error(`a recursive function with ${n} parameters has no bridge yet`);
    const late = binders([...sig.params, sig.result], { eq: true, late: true });
    const adm = `${P.map(p => `apply Lean.Order.admissible_pi; intro ${p}; `).join("")}exact ${P.reduceRight((inner, p, i) => `Lean.Order.admissible_apply (fun _ (f : ${sig.params.slice(i + 1).map(t => `${plain(t)} → `).join("")}Result ${res}) => DWLP failOk (f ${P.slice(i + 1).join(" ")}) (fun r _ => ${key}_Q ${P.join(" ")} r) ()) ${p} (${inner})`, "DWLP.admissible failOk _ ()")}`;
    const indHead = !recursive ? "" : `def ${key}_Q ${tv} ${sig.params.map((t, i) => `(p${i} : ${plain(t)})`).join(" ")} (r : ${res}) : Prop :=
  ∀ h ${Vs.join(" ")}, ${sig.params.map((t, i) => `rep (α := ${leanType(t)}) h p${i} v${i} → `).join("")}${run}
theorem ${key}_ind_sim ${late} {g : ${sig.params.map(t => `${plain(t)} → `).join("")}Result ${res}}
    (ih : ∀ ${P.join(" ")} r, g ${P.join(" ")} = ok r → ${key}_Q ${P.join(" ")} r)
    {s ${sig.params.map((_, i) => `e${i}`).join(" ")}} ${typed} {r : ${res}} ${sig.params.map((t, i) => `(h${i} : SimE (α := ${leanType(t)}) prog s e${i} p${i})`).join(" ")}
    (hr : g ${P.join(" ")} = ok r) : SimE (α := ${repRes}) prog s (.call ${q(key)} [${sig.params.map((_, i) => `e${i}`).join(", ")}]) r :=
  sim_call (fn := ${key}) (by simp [prog]) (args${n} ${sig.params.map((_, i) => `h${i}`).join(" ")}) (by
    rintro _ _ ⟨${Vs.join(", ")}, rfl, ${sig.params.map((_, i) => `r${i}`).join(", ")}⟩
    exact ih ${sig.params.map(() => "_").join(" ")} _ hr _ ${sig.params.map(() => "_").join(" ")} ${sig.params.map((_, i) => `r${i}`).join(" ")})
macro_rules | \`(tactic| s_call) => \`(tactic| (apply ${key}_ind_sim (by assumption); ${sig.params.map(() => "sim';").join(" ")} assumption))
`;
    const ind = !recursive ? "" : indHead + `unseal Aeneas.Std.Result in
theorem ${key}_ind ${tv} : ∀ ${P.join(" ")}, DWLP failOk (${sig.lean} ${P.join(" ")}) (fun r _ => ${key}_Q ${P.join(" ")} r) () := by
  apply ${sig.lean}.fixpoint_induct (motive := fun g => ∀ ${P.join(" ")}, DWLP failOk (g ${P.join(" ")}) (fun r _ => ${key}_Q ${P.join(" ")} r) ())
  · ${adm}
  · intro g ih0 ${P.join(" ")}
    have ih : ∀ ${P.join(" ")} r, g ${P.join(" ")} = ok r → ${key}_Q ${P.join(" ")} r := fun ${P.join(" ")} r e => by
      have := ih0 ${P.join(" ")}; rw [e] at this; exact DWLP.ret_iff.mp this
    clear ih0
    refine dwlp_of_ok fun r hr => ?_
    beta_reduce at hr
    intro h ${Vs.join(" ")} ${sig.params.map((_, i) => `h${i}`).join(" ")}
`;
    const proof = (indent) => `${[...constants].reverse().map(c => `try unfold ${c} at hr`).concat([
      `apply ${sig.result.kind === "void" ? "wprun_unit" : "wprun'"}`,
      `have hb : Base h ⟨${key}.env0 [${Vs.join(", ")}], h⟩ := List.prefix_refl _`,
      ...sig.params.map((t, i) => `have hv${i} : V ⟨${key}.env0 [${Vs.join(", ")}], h⟩ ${q("PARAM" + i)} (α := ${leanType(t)}) p${i} := ⟨v${i}, by simp [${key}, Fn.env0, Env.put], h${i}⟩`),
      `generalize St.mk (${key}.env0 [${Vs.join(", ")}]) h = s0 at *`,
      "have hk : Todo _ _ := hr",
      "clear hr",
      "crun"]).map(l => indent + l).join("\n")}`;
    const recBridge = `theorem ${key}_bridge ${tv} {h ${Vs.join(" ")}} ${typed} {r : ${res}} ${reps}
    (hr : ${sig.lean} ${P.join(" ")} = ok r) :
    ${run} := by
  have := ${key}_ind ${P.join(" ")}
  rw [hr] at this
  exact DWLP.ret_iff.mp this h ${Vs.join(" ")} ${sig.params.map((_, i) => `h${i}`).join(" ")}`;
    const head = recursive ? `${ind}${proof("    ")}
${recBridge}` : `theorem ${key}_bridge ${tv} {h ${Vs.join(" ")}} ${typed} {r : ${res}} ${reps}
    (hr : ${sig.lean} ${P.join(" ")} = ok r) :
    ${run} := by
  unfold ${sig.lean} at hr
${proof("  ")}`;
    const args = sig.params.map((t, i) => `(h${i} : SimE (α := ${leanType(t)}) prog s e${i} p${i})`).join(" ");
    const call = n > 6 ? "" : `
theorem ${key}_sim ${binders([...sig.params, sig.result], { eq: true, late: true })} {s ${P.length ? sig.params.map((_, i) => `e${i}`).join(" ") : ""}} ${typed} {r : ${res}} ${args}
    (hr : ${sig.lean} ${P.join(" ")} = ok r) : SimE (α := ${repRes}) prog s (.call ${q(key)} [${sig.params.map((_, i) => `e${i}`).join(", ")}]) r :=
  sim_call (fn := ${key}) (by simp [prog]) (${n === 0 ? "args0" : `args${n} ${sig.params.map((_, i) => `h${i}`).join(" ")}`}) (by
    rintro _ _ ${n === 0 ? "rfl" : `⟨${Vs.join(", ")}, rfl, ${sig.params.map((_, i) => `r${i}`).join(", ")}⟩`}
    exact ${key}_bridge ${sig.params.map((_, i) => `r${i}`).join(" ")} hr)
macro_rules | \`(tactic| s_call) => \`(tactic| (apply ${key}_sim; ${sig.params.map(() => "sim';").join(" ")} assumption))
macro_rules | \`(tactic| sim_read) => \`(tactic| (apply ${key}_sim; ${sig.params.map(() => "sim';").join(" ")} assumption))`;
    const params = JSON.parse(`[${lean.slice(lean.indexOf(`def ${key} : Fn`)).match(/params := \[(.*?)\]/)[1]}]`);
    const fix = t => t.replaceAll(/"PARAM(\d+)"/g, (_, i) => q(params[i]));
    // A member of a `mutual` block: each call to a member is bridged by the motive the fixpoint
    // induction gives for it, and every member's step is proved in each member's induction.
    if (group) {
      const sim = indHead
        .replace(`(ih : ∀ ${P.join(" ")} r, g ${P.join(" ")} = ok r → ${key}_Q ${P.join(" ")} r)`, `(ih : ∀ ${P.join(" ")}, DWLP failOk (g ${P.join(" ")}) (fun r _ => ${key}_Q ${P.join(" ")} r) ())`)
        .replace(`    exact ih ${P.map(() => "_").join(" ")} _ hr _`, `    have := ih ${P.join(" ")}; rw [hr] at this; exact DWLP.ret_iff.mp this _`)
        .replace(`theorem ${key}_ind_sim`, `unseal Aeneas.Std.Result in\ntheorem ${key}_ind_sim`);
      group.parts.push({ key, sig, P, adm, bridge: fix(recBridge) + call,
        motive: `fun g => ∀ ${P.join(" ")}, DWLP failOk (g ${P.join(" ")}) (fun r _ => ${key}_Q ${P.join(" ")} r) ()`,
        step: fix(`  · intros
    rename_i ${P.join(" ")}
    refine dwlp_of_ok fun r hr => ?_
    beta_reduce at hr
    intro h ${Vs.join(" ")} ${sig.params.map((_, i) => `h${i}`).join(" ")}
${proof("    ")}`) });
      const pre = (loopText ? loopText + "\n" : "") + fix(sim);
      if (group.parts.length < group.size) return pre;
      return pre + "\n" + group.parts.map(o => `unseal Aeneas.Std.Result in
theorem ${o.key}_ind : ∀ ${o.P.join(" ")}, DWLP failOk (${o.sig.lean} ${o.P.join(" ")}) (fun r _ => ${o.key}_Q ${o.P.join(" ")} r) () := by
  apply ${o.sig.lean}.fixpoint_induct ${group.parts.map((m, j) => `(motive_${j + 1} := ${m.motive})`).join(" ")}
${group.parts.map(m => `  · ${m.adm}`).join("\n")}
${group.parts.map(m => m.step).join("\n")}
${o.bridge}`).join("\n\n");
    }
    return (loopText ? loopText + "\n" : "") + head.replaceAll(/"PARAM(\d+)"/g, (_, i) => q(params[i])) + call;
  });
  const core = lean.replace(/^import Core\nopen Core\n/, "").replace(/^namespace Gen\n/m, "").replace(/^end Gen\n/m, "");
  return { keys: coreNames, text: `import Spike.Tac
open Aeneas Aeneas.Std Result Core Core.TyRep Aeneas.Data.Coinductive
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
