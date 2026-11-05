import Spike.Sim
open Aeneas Aeneas.Std Result

/-! The general proof. `vsplit` walks the typed function: each `let` becomes a hypothesis,
and each `if` or `match` becomes one case per path. `crun` then walks Core, one statement at
a time. New rules are added with `macro_rules`, so a type brings its own rules. -/
namespace Core

syntax "isnone" : tactic
macro_rules | `(tactic| isnone) => `(tactic| first | rfl | assumption | (simp_all; done))
syntax "known" : tactic
macro_rules | `(tactic| known) => `(tactic| first | assumption | trivial | omega | (simp_all; done))
syntax "refuted" : tactic
macro_rules | `(tactic| refuted) => `(tactic| first | contradiction | omega | (simp_all; done))

syntax "vsplit " ident : tactic
macro_rules
  | `(tactic| vsplit $h:ident) => `(tactic| first
    | (revert $h:ident; refine Core.ok_intro ?_; intro e; subst e)
    | (revert $h:ident; exact Core.fail_intro)
    | ((revert $h:ident; refine Core.bind_intro ?_; intro tmp hx hk; vsplit hx) <;> vsplit hk)
    | (revert $h:ident; refine Core.ite_intro ?_ ?_ <;> (intro hc hk; vsplit hk))
    | (split at $h:ident <;> vsplit $h)
    | (rw [Core.unwrap_iff] at $h:ident)
    | skip)

syntax "sim" : tactic
syntax "sim'" : tactic
syntax "sim0" : tactic
syntax "simb" : tactic
syntax "simc" : tactic
syntax "post" : tactic
syntax "crun" : tactic
syntax "siml" : tactic
syntax "simf" : tactic

macro_rules | `(tactic| post) => `(tactic| first | exact Core.post_ret | (apply Core.post_seq; post))

-- Variables, literals and options. Later rules are tried first.
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.some_inv; apply SimE.var; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.var; assumption))
macro_rules | `(tactic| sim0) => `(tactic| exact SimE.lit_num ⟨_, by decide, by decide⟩ rfl)
macro_rules | `(tactic| sim0) => `(tactic| exact SimE.lit_num _ rfl)
macro_rules | `(tactic| sim0) => `(tactic| exact SimE.lit_big _)
macro_rules | `(tactic| sim0) => `(tactic| exact SimE.lit_bool _)
macro_rules | `(tactic| sim0) => `(tactic| exact SimE.lit_str _)
macro_rules | `(tactic| sim0) => `(tactic| exact SimE.lit_undef (by simp [nothingOk]))
macro_rules | `(tactic| sim0) => `(tactic| exact SimE.lit_null (by simp [nothingOk]))

-- Arithmetic and strings
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.add; sim'; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.sub; sim'; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.mul; sim'; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.neg; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.concat; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.badd; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.bsub; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.bmul; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.bdiv; sim'; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.brem; sim'; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.len_str; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.len_arr; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.at_; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimC.startsWith; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimC.endsWith; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimC.strIncludes; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimC.includes_str; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.trim; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.trimStart; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.trimEnd; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.toLower; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.toUpper; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.of_c; simc))

-- Branching values
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.cond_t; simb; known; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.cond_f; simb; known; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.or_true; sim'; simb; known))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.or_false; simb; known; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.and_true; simb; known; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.and_false; sim'; simb; known))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.coalesce_none; sim'; isnone; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.coalesce_some; sim'; infer_instance))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.optField_none; sim'; isnone; simp [nothingOk]))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.array; siml))
macro_rules | `(tactic| siml) => `(tactic| exact siml_nil)
macro_rules | `(tactic| siml) => `(tactic| (apply siml_cons; sim'; siml))

-- Adjusting the type without descending, so these can't call each other forever.
macro_rules | `(tactic| sim') => `(tactic| (apply SimE.of_eq_some; assumption; sim0))
macro_rules | `(tactic| sim') => `(tactic| (apply SimE.unwrap; sim0; assumption))
macro_rules | `(tactic| sim') => `(tactic| (apply SimE.up up_undef; sim0))
macro_rules | `(tactic| sim') => `(tactic| (apply SimE.up up_null; sim0))
macro_rules | `(tactic| sim') => `(tactic| (apply SimE.some; sim0))
macro_rules | `(tactic| sim') => `(tactic| sim0)

-- A known target may differ from what the code computes only by shape.
macro_rules | `(tactic| sim) => `(tactic| (apply SimE.conv; sim'; simp [List.append_assoc]))
macro_rules | `(tactic| sim) => `(tactic| sim')

-- Truth
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.lt; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.gt; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.le; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ge; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ne; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq_str; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ne_str; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq_bool; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ne_bool; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.lt_big; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.gt_big; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.le_big; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ge_big; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq_big; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ne_big; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimB.lt_str; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimB.gt_str; sim'; sim'))
macro_rules | `(tactic| simc) => `(tactic| (apply SimB.isNullish_none; sim'; isnone))
macro_rules | `(tactic| simc) => `(tactic| (apply SimB.isNullish_some; sim'; infer_instance))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq_undef_none; sim'; isnone))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq_null_none; sim'; isnone))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ne_undef_none; sim'; isnone))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ne_null_none; sim'; isnone))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq_nothing_some rfl; sim'; infer_instance))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ne_nothing_some rfl; sim'; infer_instance))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.not; simb))

macro_rules | `(tactic| simb) => `(tactic| (apply SimB.none; sim'; isnone))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.obj; sim'; infer_instance))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.big; sim'))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.num; sim'))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.str; sim'))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.bool; sim'))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.not; simb))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.and_t; simb; known; simb))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.and_f; simb; known))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.or_f; simb; known; simb))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.or_t; simb; known))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.and_both; simb; simb))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.or_both; simb; simb))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.of_c; simc))

-- Statements
macro_rules | `(tactic| crun) => `(tactic| (apply step_nil; crun))
macro_rules | `(tactic| crun) => `(tactic| (apply step_set; sim; intro s' hv hk; carry hk; clear hk; crun))
macro_rules | `(tactic| crun) => `(tactic| (apply step_expr; sim; intro s' hk; carry hk; clear hk; crun))
macro_rules | `(tactic| crun) => `(tactic| (apply step_ret; post; assumption; sim))
macro_rules | `(tactic| crun) => `(tactic| (
  apply step_ite
  simb
  intro hp s' hk; first | (exfalso; refuted) | (carry hk; clear hk; crun)
  intro hp s' hk; first | (exfalso; refuted) | (carry hk; clear hk; crun)))

end Core
