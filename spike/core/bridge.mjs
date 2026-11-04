// Writes one bridge theorem per function. The only inputs are the function's signature
// and the shape of its Core body: no proof text here is specific to any function.
import { readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { lower } from "./lower.mjs";
const { translate } = await import("/Users/nhestrompia/.t3/worktrees/proofci/typescript-support/typescript/translate.mjs");
const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, "work");
const targets = process.argv.slice(2);
const view = translate({ root, module: "View", targets });
const { names, info, lean } = lower(root, targets);
const fnAttr = [...lean.matchAll(/^def (\S+) : Fn/gm)].map(m => `attribute [simp] Gen.${m[1]}`).join("\n");

const records = new Map();
const scan = t => {
  if (t.kind === "record") { if (!records.has(t.lean)) { records.set(t.lean, t); t.fields.forEach(f => scan(f.type)); } }
  if (t.kind === "optional") scan(t.inner);
  if (t.kind === "array") scan(t.item);
};
for (const s of Object.values(view.signatures)) { s.params.forEach(scan); scan(s.result); }
const enums = new Map();
const scanE = t => {
  if (t.kind === "enum") enums.set(t.lean, t);
  if (t.kind === "record") t.fields.forEach(f => scanE(f.type));
  if (t.kind === "optional") scanE(t.inner);
  if (t.kind === "array") scanE(t.item);
};
for (const s of Object.values(view.signatures)) { s.params.forEach(scanE); scanE(s.result); }
const short = n => n.replace(/\W/g, "_");
const enumInstances = [...enums.values()].map(e => {
  const units = t => `[${[...t].map(c => c.charCodeAt(0)).join(", ")}]`;
  return `instance : Enc ${e.lean} := ⟨fun _ a v => match a with\n${e.tags.map(t => `  | .${t.lean} => v = .str ${units(t.tag)}`).join("\n")}⟩\n${e.tags.map(t =>
    `@[simp] theorem enc_${short(e.lean)}_${t.tag} {h v} : Enc.enc h ${e.lean}.${t.lean} v ↔ v = .str ${units(t.tag)} := Iff.rfl`).join("\n")}`;
}).join("\n\n");
const instances = enumInstances + "\n\n" + [...records.values()].map(r => {
  const body = v => `∃ l fs, v = .ref l ∧ h[l]? = some (.record fs)${r.fields.map(f => ` ∧\n  Enc.enc h a.${f.lean} ((fs.lookup ${JSON.stringify(f.name)}).getD .undef)`).join("")}`;
  return `instance : Enc ${r.lean} := ⟨fun h a v => ${body()}⟩\n@[simp] theorem enc_${short(r.lean)} {h} {a : ${r.lean}} {v} : Enc.enc h a v ↔ ${body()} := Iff.rfl`;
}).join("\n\n");

// Takes apart `hyp : Enc.enc h name value`.
function open_(type, hyp, tag) {
  const scalar = { number: "enc_num", bigint: "enc_big", boolean: "enc_bool", string: "enc_str" }[type.kind];
  if (scalar) return [`  simp only [${scalar}] at ${hyp}`, `  subst ${hyp}`];
  if (type.kind === "enum") return [`  cases p${tag} <;> simp only [${type.tags.map(t => `enc_${short(type.lean)}_${t.tag}`).join(", ")}] at ${hyp} <;> subst ${hyp}`];
  if (type.kind === "array") return [`  simp only [enc_list] at ${hyp}`, `  obtain ⟨l${tag}, vs${tag}, rfl, harr${tag}, hf${tag}⟩ := ${hyp}`];
  if (type.kind === "record") {
    const fields = type.fields.map((_, i) => `f${tag}${i}`);
    return [`  simp only [enc_${short(type.lean)}] at ${hyp}`, `  obtain ⟨l${tag}, fs${tag}, rfl, hl${tag}, ${fields.join(", ")}⟩ := ${hyp}`,
      ...type.fields.flatMap((f, i) => { const r = { number: "enc_num", string: "enc_str", bigint: "enc_big", boolean: "enc_bool" }[f.type.kind]; return r ? [`  simp only [${r}] at f${tag}${i}`] : []; })];
  }
  throw new Error(`no encoding for ${type.kind}`);
}
const options = (type, tag) => type.kind !== "record" ? [] : type.fields.flatMap((f, i) => f.type.kind !== "optional" ? [] : [
  `  all_goals (try simp only [*, enc_none, enc_some, enc_num] at f${tag}${i})`, `  all_goals (try rcases f${tag}${i} with f${tag}${i} | f${tag}${i})`]);

// An optional parameter is taken apart in each of its cases.
function optionalParam(t, i) {
  if (t.kind !== "optional") return open_(t, `h${i}`, `${i}`);
  const inner = open_(t.inner, `h${i}`, `${i}`).map(l => l.replace(/^  /, ""));
  return [`  rcases p${i} with _ | p${i}`, `  on_goal 2 =>`, `    simp only [enc_some] at h${i}`, ...inner.map(l => `    ${l}`), `  on_goal 1 =>`, `    rcases h${i} with h${i} | h${i} <;> subst h${i}`];
}

const uses = key => [...lean.slice(lean.indexOf(`def ${key} :`)).split("\n\n")[0].matchAll(/\.call "([^"]+)"/g)].map(m => m[1]);
const out = [];
for (const [target, sig] of Object.entries(view.signatures)) {
  const key = names[target];
  const P = sig.params.map((_, i) => `p${i}`), V = sig.params.map((_, i) => `v${i}`);
  // Everything the shallow body calls, found by reading the view.
  const unfolds = [];
  const visit = name => {
    if (unfolds.includes(name)) return;
    unfolds.push(name);
    const start = view.source.indexOf(`def ${name} `);
    if (start < 0) return;
    const text = view.source.slice(start, view.source.indexOf("\n\n", start)).replace(/^[^\n]*:= do/, "");
    for (const m of text.matchAll(/_root_\.([\w.]+)/g)) if (view.source.includes(`def ${m[1]} `)) visit(m[1]);
  };
  visit(sig.lean);
  const lines = [`theorem ${key}_bridge {h ${P.join(" ")} ${V.join(" ")} r}`,
    ...sig.params.map((_, i) => `    (h${i} : Enc.enc h p${i} v${i})`),
    `    (hr : ${sig.lean} ${P.join(" ")} = ok r) :`,
    `    WpRun prog ${key} [${V.join(", ")}] h fun v s => h <+: s.heap ∧ Enc.enc s.heap r v := by`,
    ...sig.params.flatMap((t, i) => optionalParam(t, i)),
    `  all_goals unfold ${unfolds.join(" ")} at hr`, "  all_goals apply wprun", `  all_goals simp only [${key}]`, "  all_goals try simp only [bind_ok, Aeneas.Std.bind_assoc] at hr"];
  const loop = info[key];
  if (!loop) lines.push("  all_goals shallow", "  all_goals core_run");
  else {
    const arr = sig.params.findIndex(t => t.kind === "array");
    const item = sig.params[arr].item;
    const carried = loop.carried[0];
    const facts = sig.params.map((t, i) => `s.env ${JSON.stringify(key_param(i))} = some ${value(t, i)}`).join(" ∧ ");
    function key_param(i) { return JSON.parse(`[${lean.slice(lean.indexOf(`def ${key} :`)).match(/params := \[(.*?)\]/)[1]}]`)[i]; }
    function value(t, i) { return t.kind === "array" ? `(.ref l${i})` : t.kind === "number" ? `(.num p${i}.val)` : `v${i}`; }
    const R = `(fun a s => s.heap = h ∧ ${facts} ∧ ∃ w, s.env ${JSON.stringify(carried)} = some w ∧ Enc.enc h a w)`;
    lines.push("  revert hr; refine Core.bind_intro ?_; intro res hl hr", "  shallow", "  all_goals core_run",
      `  refine wp_iter_loop hl hf${arr} ${R} ${R} ?_ ?_ (fun _ _ hR => hR.1) harr${arr} ?_ ?_`,
      `  · refine ⟨rfl, ?_⟩`, "    simp [Env.put, Fn.env0, *]", "    first | done | exact enc_at hf" + arr + " 0",
      "  · rintro s ⟨hh, " + sig.params.map((_, i) => `e${i}`).join(", ") + ", w, hw, hwe⟩", "    try simp only [enc_num] at hwe", "    try subst hwe", "    try simp only [enc_some] at hwe",
      ...(sig.result.kind === "record" ? open_(sig.result, "hwe", "r").map(l => `  ${l}`) : []), "    core_run",
      "  · intro a s y hR hb", "    simp at hb", "    exact ⟨a, hb.symm, hR⟩",
      "  · rintro q rest a s item y ⟨hh, " + sig.params.map((_, i) => `e${i}`).join(", ") + ", w, hw, hwe⟩ hq hr", "    try simp only [enc_num] at hwe", "    try subst hwe",
      ...open_(item, "hq", "q").map(l => `  ${l}`),
      "    dsimp only at hr", "    shallow", ...options(item, "q").map(l => `  ${l}`), "    all_goals core_run");
  }
  out.push(lines.join("\n"));
}
writeFileSync(join(here, "Spike/Bridges.lean"), `import Spike.WP
open Core Aeneas Aeneas.Std Result Gen

${fnAttr}
attribute [simp] Gen.prog

${instances}

${out.join("\n\n")}
`);
