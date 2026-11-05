import Spike.Sim
open Aeneas Aeneas.Std Result

/-! The general proof. `vsplit` walks the typed function: each `let` becomes a hypothesis,
and each `if` or `match` becomes one case per path. `crun` then walks Core, one statement at
a time. New rules are added with `macro_rules`, so a type brings its own rules. -/
namespace Core

syntax "isnone" : tactic
macro_rules | `(tactic| isnone) => `(tactic| first | rfl | assumption | (simp_all; done))
syntax "known" : tactic
macro_rules | `(tactic| known) => `(tactic| first | assumption | trivial | omega | tauto | (simp_all; done))
syntax "refuted" : tactic
macro_rules | `(tactic| refuted) => `(tactic| first | contradiction | omega | tauto | (simp_all; done) | (simp only [decide_eq_true_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at *; first | omega | tauto))

syntax "vsplit " ident : tactic
macro_rules
  | `(tactic| vsplit $h:ident) => `(tactic| first
    | (revert $h:ident; with_reducible refine Core.ok_intro ?_; intro e; subst e)
    | (revert $h:ident; with_reducible exact Core.fail_intro)
    | ((revert $h:ident; with_reducible refine Core.bind_intro ?_; intro tmp hx hk; vsplit hx) <;> vsplit hk)
    | (revert $h:ident; with_reducible refine Core.ite_intro ?_ ?_ <;> (intro hc hk; vsplit hk))
    | (split at $h:ident <;> vsplit $h)
    | (rw [Core.unwrap_iff] at $h:ident)
    | skip)

syntax "sim" : tactic
syntax "sim'" : tactic
syntax "sim0" : tactic
syntax "sim_read" : tactic
syntax "sim_v" : tactic
syntax "simb" : tactic
syntax "simc" : tactic
syntax "post" : tactic
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
macro_rules | `(tactic| sim0) => `(tactic| exact SimE.len_lit _ rfl)
macro_rules | `(tactic| sim0) => `(tactic| exact SimE.len_lit ⟨_, by decide, by decide⟩ rfl)
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.len_str; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.len_arr; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.at_; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimC.startsWith; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimC.endsWith; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimC.strIncludes; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimC.includes_str; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.slice_str; sim'; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.sliceFrom_str; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.slice_arr; sim'; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.sliceFrom_arr; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.strIndexOf; sim'; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.charAt; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.numStr; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.min; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.max; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.abs; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.join; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.includes_arr; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.split; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| exact SimE.nil_str)
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.trim; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.trimStart; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.trimEnd; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.toLower; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.toUpper; sim'; assumption))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.of_c; simc))

-- Branching values
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.cond_ite; simb; sim'; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.cond_t; simb; known; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.cond_f; simb; known; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.or_true; sim'; simb; known))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.or_false; simb; known; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.and_true; simb; known; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.and_false; sim'; simb; known))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.coalesce_none; sim'; isnone; sim'))
macro_rules | `(tactic| sim0) => `(tactic| (apply SimE.coalesce_some; sim_v; infer_instance))
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

-- A value of unknown type that isn't nullish here, so an option is read through.
macro_rules | `(tactic| sim_v) => `(tactic| first | (apply SimE.some_inv; apply SimE.var; assumption) | (apply SimE.unwrap; sim0; assumption) | sim0)

-- A known target may differ from what the code computes only by shape.
macro_rules | `(tactic| sim) => `(tactic| (apply SimE.conv; sim'; first | rfl | (simp [List.append_assoc]; done) | (simp_all; done)))
macro_rules | `(tactic| sim) => `(tactic| sim')

-- Truth
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq_opt; sim_read; sim'; infer_instance))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.of_bool; sim_read))
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
macro_rules | `(tactic| simc) => `(tactic| (apply SimB.isNullish_some; sim_v; infer_instance))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq_undef_none; sim'; isnone))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq_null_none; sim'; isnone))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ne_undef_none; sim'; isnone))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ne_null_none; sim'; isnone))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.eq_nothing_some; rfl; sim_v; infer_instance))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.ne_nothing_some; rfl; sim_v; infer_instance))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.not; simb))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.and; simc; simc))
macro_rules | `(tactic| simc) => `(tactic| (apply SimC.or; simc; simc))
macro_rules | `(tactic| sim_read) => `(tactic| (apply SimE.some_inv; apply SimE.var; assumption))
macro_rules | `(tactic| sim_read) => `(tactic| (apply SimE.var; assumption))
macro_rules | `(tactic| sim_read) => `(tactic| exact SimE.lit_bool _)
macro_rules | `(tactic| sim_read) => `(tactic| (apply SimC.startsWith; sim'; sim'))
macro_rules | `(tactic| sim_read) => `(tactic| (apply SimC.endsWith; sim'; sim'))
macro_rules | `(tactic| sim_read) => `(tactic| (apply SimC.strIncludes; sim'; sim'))
macro_rules | `(tactic| sim_read) => `(tactic| (apply SimC.includes_str; sim'; sim'))
macro_rules | `(tactic| sim_read) => `(tactic| (apply SimE.includes_arr; sim'; sim'))

macro_rules | `(tactic| simb) => `(tactic| (apply SimB.none; sim'; isnone))
macro_rules | `(tactic| simb) => `(tactic| (apply SimB.obj; sim_v; infer_instance))
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

-- Statements. Core and the typed function advance together: `vdrain` consumes what the next
-- statement needs, and the statement's kind then picks one rule.
syntax "c_nil" : tactic
syntax "c_set" : tactic
syntax "c_expr" : tactic
syntax "c_ret" : tactic
syntax "c_ite" : tactic
syntax "c_ite_lock" : tactic
syntax "c_join" : tactic
syntax "c_for" : tactic
syntax "c_brk" : tactic
syntax "c_cont" : tactic
syntax "v_split" : tactic
syntax "v_ok" : tactic
syntax "v_leaf" : tactic
syntax "v_fail" : tactic
syntax "v_ite" : tactic
syntax "seq_out" : tactic
syntax "vall" : tactic
syntax "crun" : tactic
open Lean Elab Tactic Meta

/-- The pending typed step: the head of its computation and the binder of what follows. -/
def todoHead : TacticM (Option (Lean.Expr × Option Name)) := withMainContext do
  for d in (← getLCtx).decls.toList.reverse do
    let some d := d | continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOf ``Core.Todo do continue
    let m := ty.getArg! 1
    if m.isAppOf ``Aeneas.Std.bind || m.isAppOf ``Bind.bind then
      let n := m.getAppNumArgs
      let inner := m.getArg! (n - 2)
      let f := m.getArg! (n - 1)
      return some (inner, if f.isLambda then some f.bindingName! else none)
    return some (m, none)
  return none

def revertTodo : TacticM Unit := withMainContext do
  for d in (← getLCtx).decls.toList.reverse do
    let some d := d | continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Core.Todo then
      let (_, g) ← (← getMainGoal).revert #[d.fvarId]
      replaceMainGoal [g]
      return

def headIs (e : Lean.Expr) (n : Name) : Bool := e.getAppFn.isConstOf n
def isBranch (e : Lean.Expr) : MetaM Bool := do
  return headIs e ``ite || headIs e ``dite || (← Lean.Meta.isMatcherApp e)

elab "v_step" : tactic => do
  revertTodo
  evalTactic (← `(tactic| with_reducible refine Core.todo_bind ?_))
  evalTactic (← `(tactic| (intro tmp hx hk; first | (revert hx; with_reducible refine Core.ok_intro ?_; intro e; subst e) | (rw [Core.unwrap_iff] at hx) | skip)))

/-- Consumes pure steps up to the end of one source statement. -/
partial def vdrain : TacticM Unit := do
  let some (m, binder) ← todoHead | return
  if headIs m ``Aeneas.Std.Result.fail then evalTactic (← `(tactic| v_fail)); return
  if binder.isNone then
    if headIs m ``Aeneas.Std.Result.ok then evalTactic (← `(tactic| v_ok))
    return
  if (← isBranch m) || headIs m ``Aeneas.Std.loop then return
  evalTactic (← `(tactic| v_leaf))
  if headIs m ``Aeneas.Std.Result.ok then
    if let some b := binder then
      unless b.toString.startsWith "tmp" || b.isInternal do return
  if (← getGoals).isEmpty then return
  vdrain

elab "vall_go" : tactic => do
  for _ in [0:200] do
    let some (m, binder) ← todoHead | return
    if binder.isNone || (← isBranch m) || headIs m ``Aeneas.Std.loop then return
    evalTactic (← `(tactic| v_leaf))

/-- A statement ends the walk only through a rule below. -/
elab "crun_go" : tactic => withMainContext do
  vdrain
  if (← getGoals).isEmpty then return
  withMainContext do
  let t ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
  unless t.isAppOf ``Core.Wp do throwError "STUCK, not a Core goal"
  let cs ← whnfD (t.getArg! 2)
  let kind ← if cs.isAppOf ``List.nil then pure `nil else do
    let c ← whnfD (cs.getArg! 1)
    pure c.getAppFn.constName!
  let pending ← todoHead
  let branch ← match pending with
    | some (m, _) => isBranch m
    | none => pure false
  let tail := match pending with
    | some (_, b) => b.isNone
    | none => false
  let tac ← match kind with
    | `nil => if branch then `(tactic| (focus (v_split; all_goals crun))) else `(tactic| c_nil)
    | ``Stmt.ite =>
      if branch && tail then
        match pending with
        | some (m, _) =>
          if headIs m ``ite then `(tactic| c_ite_lock) else `(tactic| (focus (v_split; all_goals crun)))
        | none => `(tactic| c_ite)
      else if branch then `(tactic| first | c_join | (v_split; all_goals crun))
      else `(tactic| c_ite)
    | ``Stmt.forOf => `(tactic| c_for)
    | ``Stmt.brk => `(tactic| c_brk)
    | ``Stmt.cont => `(tactic| c_cont)
    | n =>
      if branch then `(tactic| (focus (v_split; all_goals crun)))
      else match n with
        | ``Stmt.set => `(tactic| c_set)
        | ``Stmt.expr => `(tactic| c_expr)
        | ``Stmt.ret => `(tactic| c_ret)
        | ``Stmt.throw => throwError "STUCK on a throw the typed function doesn't take"
        | n => throwError "STUCK on statement {n}"
  evalTactic tac

macro_rules | `(tactic| crun) => `(tactic| crun_go)
macro_rules | `(tactic| vall) => `(tactic| vall_go)

macro_rules | `(tactic| v_leaf) => `(tactic| v_step)
elab "v_ok_go" : tactic => do
  revertTodo
  evalTactic (← `(tactic| with_reducible refine Core.todo_ok ?_))
  evalTactic (← `(tactic| intro e; subst e))
elab "v_fail_go" : tactic => do
  revertTodo
  evalTactic (← `(tactic| with_reducible exact Core.todo_fail))
macro_rules | `(tactic| v_ok) => `(tactic| v_ok_go)
macro_rules | `(tactic| v_fail) => `(tactic| v_fail_go)
elab "v_ite_go" : tactic => do
  revertTodo
  evalTactic (← `(tactic| with_reducible refine Core.todo_ite ?_ ?_ <;> intro hc hk))
elab "v_decide_go" : tactic => do
  revertTodo
  evalTactic (← `(tactic| first
    | (with_reducible refine Core.todo_pos ?_ ?_; known; intro hk)
    | (with_reducible refine Core.todo_neg ?_ ?_; known; intro hk)
    | (with_reducible refine Core.todo_ite ?_ ?_ <;> intro hc hk)))
elab "v_split_go" : tactic => do
  revertTodo
  let some (_, _) := some (0, 0) | return
  evalTactic (← `(tactic| first
    | (with_reducible refine Core.todo_bind ?_; intro tmp hx hk; vsplit hx)
    | (with_reducible refine Core.todo_ite ?_ ?_ <;> intro hc hk)
    | (intro hz; unfold Todo at hz; split at hz <;> (have hk : Todo _ _ := hz; clear hz))))
macro_rules | `(tactic| v_split) => `(tactic| v_split_go)
macro_rules | `(tactic| seq_out) => `(tactic| first | (apply seq_exit; simp; seq_out) | skip)

macro_rules | `(tactic| c_nil) => `(tactic| (apply step_nil; crun))
macro_rules | `(tactic| c_set) => `(tactic| (apply step_set; (first | sim | (vall; sim) | fail "STUCK"); intro s' hv hk; carry hk; clear hk; crun))
macro_rules | `(tactic| c_expr) => `(tactic| (apply step_expr; (first | sim | (vall; sim) | fail "STUCK"); intro s' hk; carry hk; clear hk; crun))
macro_rules | `(tactic| c_ret) => `(tactic| (apply step_ret; post; assumption; first | sim | (vall; sim) | fail "STUCK"))
macro_rules | `(tactic| c_ite) => `(tactic| (
  apply step_ite
  first | simb | (vall; simb) | fail "STUCK"
  (focus (intro hp s' hk; first | (exfalso; refuted) | (carry hk; clear hk; crun)))
  (focus (intro hp s' hk; first | (exfalso; refuted) | (carry hk; clear hk; crun)))))
macro_rules | `(tactic| c_ite_lock) => `(tactic| (
  apply step_ite
  first | simb | (vall; simb) | fail "STUCK"
  (focus (intro hp s' hk; carry hk; clear hk; v_decide_go; all_goals (first | (exfalso; refuted) | crun)))
  (focus (intro hp s' hk; carry hk; clear hk; v_decide_go; all_goals (first | (exfalso; refuted) | crun)))))
macro_rules | `(tactic| c_brk) => `(tactic| (apply step_brk; seq_out; fail "STUCK break"))
macro_rules | `(tactic| c_cont) => `(tactic| (apply step_cont; seq_out; fail "STUCK continue"))
macro_rules | `(tactic| c_join) => `(tactic| fail)

end Core
