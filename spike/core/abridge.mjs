// The bridge for an `async` function: its typed view (an `Eff` computation), Core's reading of it
// (CoreAsync), and a theorem that every run of the view is a run of Core with the same outcome and
// history, for every pair of oracles that answer related calls alike (Spike/ASim.lean).
import { lower } from "./lower.mjs";
import { translate } from "../../typescript/translate.mjs";
import { leanType, plain, recordShapes, enumRules, taggedRules, recordRules } from "./bridge3.mjs";

const q = JSON.stringify;
const BASIC = new Set(["string", "number", "boolean", "void", "bigint", "enum"]);
const encodable = t => BASIC.has(t.kind) || (t.kind === "optional" && encodable(t.inner)) || (t.kind === "array" && encodable(t.item))
  || (t.kind === "record" && !t.args && (t.declared ?? t.fields).every(f => encodable(f.type)))
  || (t.kind === "tagged" && !t.args && t.variants.every(v => v.fields.every(f => encodable(f.type))));

// The encodings of the records, enums and tagged unions a function's values and answers use, as bridge3 writes them.
function typeRules(view, lean, roots) {
  const types = new Map();
  const scan = t => {
    if (t.kind === "record" || t.kind === "enum") { if (types.has(t.lean)) return; if (t.kind === "record") (t.declared ?? t.fields).forEach(f => scan(f.type)); types.set(t.lean, t); }
    if (t.kind === "tagged" && !types.has(t.lean)) { t.variants.forEach(v => v.fields.forEach(f => scan(f.type))); types.set(t.lean, t); }
    if (t.kind === "optional") scan(t.inner);
    if (t.kind === "array") scan(t.item);
  };
  roots.forEach(scan);
  for (const t of view.records()) if (t.kind === "record" && encodable(t)) scan(t);
  const shapes = recordShapes(lean);
  return [...types.values()].map(t => t.kind === "enum" ? enumRules(t) : t.kind === "tagged" ? taggedRules(t, shapes) : recordRules(t, shapes)).join("\n");
}

// The arms of `def Arg`/`def Res` in the view's world block.
function arms(source, name) {
  const at = source.indexOf(`@[reducible] def ${name} : Op → Type`);
  if (at < 0) return new Map();
  const block = source.slice(at, source.indexOf("\n\n", at));
  return new Map([...block.matchAll(/^ {2}\| \.(\S+) => (.*)$/gm)].map(m => [m[1], m[2]]));
}

// `A × B × C`, split at the top level.
function tuple(text) {
  let t = text.trim();
  if (t.startsWith("(") && t.endsWith(")")) {
    let depth = 0, whole = true;
    for (let i = 0; i < t.length; i++) {
      if (t[i] === "(") depth++;
      else if (t[i] === ")") { depth--; if (depth === 0 && i < t.length - 1) { whole = false; break; } }
    }
    if (whole) t = t.slice(1, -1);
  }
  const parts = [];
  let depth = 0, start = 0;
  for (let i = 0; i < t.length; i++) {
    if (t[i] === "(") depth++;
    else if (t[i] === ")") depth--;
    else if (depth === 0 && t.startsWith(" × ", i)) { parts.push(t.slice(start, i)); start = i + 3; }
  }
  parts.push(t.slice(start));
  return parts.map(p => p.trim());
}

export function generateAsync(root, target, paths, { viewSource, options } = {}) {
  const { names, lean } = lower(root, [target], { paths, eff: { effects: options?.effects ?? [] } });
  const key = names[target];
  if (/\.forOf |\.whileL /.test(lean)) throw new Error("a loop in async code has no bridge yet");
  if (/\.tryFinally /.test(lean)) throw new Error("`finally` in async code has no bridge yet");
  // A function awaited by another gets its theorem first; the caller's proof uses it.
  const file = target.slice(0, target.indexOf("::")), prefix = key.slice(0, key.length - target.length + file.length + 2);
  const bodies = new Map([...lean.matchAll(/^def (\S+) : AFn := ([\s\S]*?)\n\n/gm)].map(m => [m[1], m[2]]));
  const order = [], seen = new Set();
  const visit = k => {
    if (order.includes(k)) return;
    if (seen.has(k)) throw new Error("a recursive async function has no bridge yet");
    if (!bodies.has(k) || !k.startsWith(prefix)) throw new Error("an await of an async function of another file has no bridge yet");
    seen.add(k);
    for (const m of bodies.get(k).matchAll(/\.awaitFn "[^"]*" "([^"]*)"/g)) visit(m[1]);
    order.push(k);
  };
  visit(key);
  const targets = order.map(k => `${file}::${k.slice(prefix.length)}`);
  const view = translate({ root, module: "V", paths, targets, ...options });
  const sigs = targets.map(t => {
    if (view.failures[t]) throw new Error(`callee rejected: ${view.failures[t]}`);
    const sig = view.signatures[t];
    if (!sig?.async) throw new Error("not an async function");
    for (const ty of [...sig.params, sig.result]) if (!encodable(ty)) throw new Error(`no async bridge for a ${ty.kind} value yet`);
    if (sig.params.length > 2 && sig !== view.signatures[target]) throw new Error(`an await of a function with ${sig.params.length} arguments has no bridge yet`);
    return sig;
  });
  const source = (viewSource ?? view.source).replace(/^import.*\n/gm, "");
  const used = new Map(view.effectList.map(e => [e.lean, e]));
  for (const e of used.values()) {
    if (e.params.length > 2) throw new Error(`an outside call with ${e.params.length} arguments has no bridge yet`);
    for (const t of [...e.params, e.returns]) if (!encodable(t)) throw new Error(`no async bridge for a ${t.kind} answer or argument yet`);
  }
  const rules = typeRules(view, lean, [...sigs.flatMap(sig => [...sig.params, sig.result]), ...[...used.values()].flatMap(e => [...e.params, e.returns])]);
  const argArms = arms(source, "Arg"), resArms = arms(source, "Res");
  const ids = new Map((options?.effects ?? []).map(e => [e.id.replace(/[^A-Za-z0-9_]/g, "_"), e.id]));
  const ops = [...argArms.keys()];
  const opName = ops.map(o => `  | .${o} => ${q(used.get(o)?.id ?? ids.get(o) ?? o)}`);
  const argOK = ops.map(o => {
    const n = argArms.get(o).trim() === "Unit" ? 0 : tuple(argArms.get(o)).length;
    if (n === 0) return `  | .${o}, _, ds => ds = []`;
    if (n === 1) return `  | .${o}, a, ds => ∃ h v, ds = [readData 50 h v] ∧ rep h a v`;
    if (n === 2) return `  | .${o}, a, ds => ∃ h v w, ds = [readData 50 h v, readData 50 h w] ∧ rep h a.1 v ∧ rep h a.2 w`;
    return `  | .${o}, _, _ => False`;
  });
  // An operation this function doesn't call, whose answers have no encoding, answers nothing the
  // relation accepts: the theorem then covers the histories where it never answered a value.
  const resRep = ops.map(o => {
    const e = used.get(o);
    if (e) return `  | .${o} => inferInstanceAs (TyRep ${plain(e.returns)})`;
    return `  | .${o} => ⟨fun _ _ _ => False, fun _ h => h⟩`;
  });
  const W = "Proofci.Effects.world";
  const theorem = (key, sig) => {
    const P = sig.params.map((_, i) => `p${i}`), Vs = sig.params.map((_, i) => `v${i}`);
    const params = JSON.parse(`[${bodies.get(key).match(/params := \[(.*?)\]/)[1]}]`);
    const typed = sig.params.map((t, i) => `{p${i} : ${plain(t)}}`).join(" ");
    const reps = sig.params.map((t, i) => `(h${i} : rep (α := ${leanType(t)}) h p${i} v${i})`).join(" ");
    const s0 = `(⟨⟨${key}.env0 [${Vs.join(", ")}], h⟩, hc⟩ : AS)`;
    return `set_option maxHeartbeats 4000000 in
theorem ${key}_abridge {ov oc} (hO : ORel opName ArgOK ov oc) {hv hc h ${Vs.join(" ")}} ${typed} ${reps}
    (hHc : HRel opName ArgOK hv hc) {r hv'} (hr : ${sig.lean} ${P.join(" ")} ov hv = ok (r, hv')) (st : St) (hh : st.heap = h) :
    ∃ out, ARuns prog aprog oc ${key} [${Vs.join(", ")}] ⟨st, hc⟩ out ∧ ARes (opName := opName) (ArgOK := ArgOK) h r hv' out := by
  simp only [${sig.lean}, Proofci.Effects.call] at hr
  refine AW.top' (ARes.not_normal opName ArgOK) (ARes.ret opName ArgOK) ?_ st hh
${sig.params.map((t, i) => `  have hV${i} : V ${s0}.st ${q(params[i])} (α := ${leanType(t)}) p${i} := ⟨v${i}, by simp [AFn.env0, ${key}, Env.put], h${i}⟩`).join("\n")}
  have hH : HRel opName ArgOK hv ${s0}.hist := hHc
  have hB : Base h ${s0}.st := List.prefix_refl _
  generalize ${s0} = s0 at *
  clear hHc ${sig.params.map((_, i) => `h${i}`).join(" ")}
  simp only [${key}]
  arun

set_option hygiene false in
macro_rules | \`(tactic| a_fnrun) => \`(tactic| exact ${key}_abridge hO ${sig.params.map((_, i) => `hr${i} `).join("")}hH heq st rfl)
`;
  };
  const text = `import Spike.ASim
${source.trimEnd()}

${lean.replace(/^import.*\n/gm, "").trimEnd()}

open Core Core.Async Gen TyRep

${rules}

def opName : ${W}.Op → String
${opName.join("\n")}

def ArgOK : (op : ${W}.Op) → ${W}.Arg op → List Data → Prop
${argOK.join("\n")}

instance resRep : ∀ op : ${W}.Op, TyRep (${W}.Res op)
${resRep.join("\n")}

${order.map((k, i) => theorem(k, sigs[i])).join("\n")}
#print axioms ${key}_abridge
`;
  return { text, theorem: `${key}_abridge` };
}
