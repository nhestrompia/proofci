// Writes bridge proofs one statement at a time. Each step is a closed term about an
// abstract state, so the proof's size is the function's size.
import { writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { lower } from "./lower.mjs";
const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, "work");
const targets = process.argv.slice(2);
const { names, lean } = lower(root, targets);
const out = [];
for (const target of targets) {
  const key = names[target], view = `src.scale.${target.split("::")[1]}`;
  const text = lean.slice(lean.indexOf(`def ${key} :`));
  const stmts = text.slice(text.indexOf("body := [") + 9, text.indexOf("] }")).split(/,\n\s+/).map(s => s.trim()).filter(Boolean);
  const L = ["  unfold " + view + " at hr", "  try simp only [bind_ok] at hr", "  apply wprun",
    `  have va : VarIs ⟨${key}.env0 [.num (F64.ofInt p0.val)], h⟩ "a" p0 := by simp [VarIs, Fn.env0, ${key}, Env.put]`,
    `  have hh : (St.mk (${key}.env0 [.num (F64.ofInt p0.val)]) h).heap = h := rfl`,
    `  generalize St.mk (${key}.env0 [.num (F64.ofInt p0.val)]) h = s0 at va hh`];
  let n = 0, t = null;                // Lean names of the state, and of `t` if it exists
  const stateful = (x, fact, stmtTerm) => {
    const s = `s${++n}`;
    L.push(`  refine step_set (a := ${x}) (${stmtTerm}) ?_`, `  intro ${s} ${fact} keeps${n}`,
      `  replace va := VarIs.keep keeps${n} (by decide) va`, `  replace hh := keeps${n}.1.trans hh`);
  };
  for (const st of stmts) {
    let m;
    if ((m = st.match(/^\.set "t" \(\.var "a"\)$/))) { stateful("p0", "vt", "NumE.var va"); t = true; }
    else if ((m = st.match(/^\.set "t" \(\.lit /))) { L.push("  -- starts at a literal"); stateful("_", "vt", "NumE.lit _ rfl"); t = true; }
    else if ((m = st.match(/^\.set "t" \(\.bin \.add \(\.var "t"\) \(\.lit /))) {
      const x = `x${n}`;
      L.push("  revert hr; refine Core.bind_intro ?_", `  intro ${x} st${n} hr`);
      L.push(`  clear_value_placeholder`);
      L.pop();
      const s = `s${++n}`;
      L.push(`  refine step_set (a := ${x}) (NumE.add (NumE.var vt) (NumE.lit _ rfl) st${n - 1}) ?_`, `  intro ${s} vt' keeps${n}`,
        `  replace va := VarIs.keep keeps${n} (by decide) va`, `  replace hh := keeps${n}.1.trans hh`, "  clear vt", "  rename' vt' => vt");
    } else if ((m = st.match(/^\.ite \(\.bin \.gt \(\.var "a"\) \(\.lit \(\.num \(F64\.ofInt \((-?\d+)\)\)\)\)\) \[\.set "t" \(\.bin \.add \(\.var "t"\) \(\.lit/))) {
      const j = `tj${n}`, s = `s${++n}`;
      L.push("  revert hr; refine Core.bind_intro ?_", `  intro ${j} hj hr`,
        `  refine step_join' (hc := SimB.gt_lit (NumE.var va)) (tj := ${j}) ?_ ?_ vt ?_`,
        "  · intro hp; rw [if_pos hp] at hj", "    exact NumE.add (NumE.var vt) (NumE.lit _ rfl) (by simpa using hj)",
        "  · intro hn; rw [if_neg hn] at hj", "    exact (Result.ok_injective hj).symm",
        `  intro ${s} vt' keeps${n}`, `  replace va := VarIs.keep keeps${n} (by decide) va`, `  replace hh := keeps${n}.1.trans hh`, "  clear vt hj", "  rename' vt' => vt");
    } else if ((m = st.match(/^\.ite \(\.bin \.eq \(\.var "a"\) \(\.lit /))) {
      L.push("  by_cases hc : _ := Classical.em _".slice(0, 0) + "  split at hr", "  · rename_i hc", "    have := Result.ok_injective hr; subst this",
        "    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl", "  rename_i hc",
        "  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_");
    } else if ((m = st.match(/^\.ret \(\.var "t"\)$/))) {
      L.push("  have := Result.ok_injective hr; subst this", "  exact step_ret (NumE.var vt) ⟨_, rfl, hh, rfl⟩");
    } else if ((m = st.match(/^\.ret \(\.lit /))) {
      L.push("  have := Result.ok_injective hr; subst this", "  exact step_ret (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩");
    } else throw new Error(`statement: ${st}`);
  }
  out.push(`theorem ${key}_bridge {h p0 r} (hr : ${view} p0 = ok r) :
    WpRun prog ${key} [.num (F64.ofInt p0.val)] h fun v s => s.heap = h ∧ Enc.enc s.heap r v := by
${L.filter(l => !l.includes("starts at a literal")).join("\n")}`);
}
writeFileSync(join(here, "Spike/Bridges2.lean"), `import Spike.Step
open Core Aeneas Aeneas.Std Result Gen
set_option maxHeartbeats 0
set_option maxRecDepth 200000

${out.join("\n\n")}
`);
