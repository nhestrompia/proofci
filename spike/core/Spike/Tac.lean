import Spike.Sim
open Aeneas Aeneas.Std Result

/-! The general proof. `vsplit` walks the typed function: each `let` becomes a hypothesis,
and each `if` or `match` becomes one case per path. `crun` then walks Core, one statement at
a time. New rules are added with `macro_rules`, so a type brings its own rules. -/
namespace Core

open Lean Elab Tactic Meta in
elab "clear_todo" : tactic => withMainContext do
  for d in (← getLCtx).decls.toList.reverse do
    let some d := d | continue
    if (← instantiateMVars d.type).isAppOf ``Core.Todo then
      replaceMainGoal [← (← getMainGoal).clear d.fvarId]
syntax "isnone" : tactic
macro_rules | `(tactic| isnone) => `(tactic| first | rfl | assumption | (simp_all; done))
syntax "known" : tactic
macro_rules | `(tactic| known) => `(tactic| first | assumption | trivial | omega | tauto | (clear_todo; simp_all; done))
syntax "refuted" : tactic
macro_rules | `(tactic| refuted) => `(tactic| first | contradiction | omega | tauto | (clear_todo; simp_all; done) | (simp_all; done) | (simp only [decide_eq_true_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at *; first | omega | tauto))

syntax "vsplit " ident : tactic
macro_rules
  | `(tactic| vsplit $h:ident) => `(tactic| first
    | (revert $h:ident; with_reducible refine Core.ok_intro ?_; intro e; subst e)
    | (revert $h:ident; with_reducible exact Core.fail_intro)
    | ((revert $h:ident; with_reducible refine Core.bind_intro ?_; intro tmp hx hk; vsplit hx) <;> vsplit hk)
    | (revert $h:ident; (with_reducible refine Core.ite_intro ?_ ?_) <;> (intro hc hk; vsplit hk))
    | (split at $h:ident <;> vsplit $h)
    | (rw [Core.unwrap_iff] at $h:ident)
    | skip)

syntax "sim" : tactic
syntax "sim'" : tactic
syntax "sim0" : tactic
syntax "sim_read" : tactic
syntax "s_hof" : tactic
syntax "s_var" : tactic
syntax "s_lit" : tactic
syntax "s_bin" : tactic
syntax "s_prim" : tactic
syntax "s_field" : tactic
syntax "s_rec" : tactic
syntax "s_call" : tactic
syntax "s_branch" : tactic
syntax "s_misc" : tactic
syntax "sim_v" : tactic
syntax "simb" : tactic
syntax "simc" : tactic
syntax "post" : tactic
syntax "siml" : tactic
syntax "simf" : tactic

macro_rules | `(tactic| post) => `(tactic| first | exact Core.post_ret | (apply Core.post_seq; post) | exact Core.post_unit | (apply Core.post_loop; intro v s h1 h2; exact ⟨h1, h2⟩) | (apply Core.post_seqs; intro v s h1 h2; exact ⟨h1, h2⟩))

-- Variables, literals and options. Later rules are tried first.
macro_rules | `(tactic| s_var) => `(tactic| (apply SimE.some_inv; apply SimE.var; assumption))
macro_rules | `(tactic| s_var) => `(tactic| (apply SimE.var; apply V.nil_cast; assumption))
macro_rules | `(tactic| s_var) => `(tactic| (apply SimE.var; assumption))
macro_rules | `(tactic| s_lit) => `(tactic| exact SimE.lit_num ⟨_, by decide, by decide⟩ rfl)
macro_rules | `(tactic| s_lit) => `(tactic| exact SimE.lit_num _ rfl)
macro_rules | `(tactic| s_lit) => `(tactic| exact SimE.lit_big _)
macro_rules | `(tactic| s_lit) => `(tactic| exact SimE.lit_bool _)
macro_rules | `(tactic| s_lit) => `(tactic| exact SimE.lit_str _)
macro_rules | `(tactic| s_lit) => `(tactic| exact SimE.lit_undef (by simp [nothingOk]))
macro_rules | `(tactic| s_lit) => `(tactic| exact SimE.lit_null (by simp [nothingOk]))

-- Arithmetic and strings
macro_rules | `(tactic| s_bin) => `(tactic| (apply SimE.concat; sim'; sim'))
macro_rules | `(tactic| s_bin) => `(tactic| (apply SimE.badd; sim'; sim'))
macro_rules | `(tactic| s_bin) => `(tactic| (apply SimE.bsub; sim'; sim'))
macro_rules | `(tactic| s_bin) => `(tactic| (apply SimE.bmul; sim'; sim'))
macro_rules | `(tactic| s_bin) => `(tactic| (apply SimE.bdiv; sim'; sim'; assumption))
macro_rules | `(tactic| s_bin) => `(tactic| (apply SimE.brem; sim'; sim'; assumption))
macro_rules | `(tactic| s_bin) => `(tactic| (apply SimE.add; sim'; sim'; assumption))
macro_rules | `(tactic| s_bin) => `(tactic| (apply SimE.sub; sim'; sim'; assumption))
macro_rules | `(tactic| s_bin) => `(tactic| (apply SimE.mul; sim'; sim'; assumption))
macro_rules | `(tactic| s_misc) => `(tactic| (apply SimE.neg; sim'; assumption))
macro_rules | `(tactic| s_misc) => `(tactic| exact SimE.len_lit _ rfl)
macro_rules | `(tactic| s_misc) => `(tactic| exact SimE.len_lit ⟨_, by decide, by decide⟩ rfl)
macro_rules | `(tactic| s_misc) => `(tactic| (apply SimE.len_str; sim'; assumption))
macro_rules | `(tactic| s_misc) => `(tactic| (apply SimE.len_arr; sim'; assumption))
macro_rules | `(tactic| s_misc) => `(tactic| (apply SimE.at_; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimC.startsWith; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimC.endsWith; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimC.strIncludes; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimC.includes_str; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.slice_str; sim'; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.sliceFrom_str; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.slice_arr; sim'; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.sliceFrom_arr; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.strIndexOf; sim'; sim'; assumption))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.charAt; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.numStr; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.min; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.max; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.abs; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.join; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.includes_arr; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.split; sim'; sim'))
macro_rules | `(tactic| s_misc) => `(tactic| exact SimE.nil_str)
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.trim; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.trimStart; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.trimEnd; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.toLower; sim'; assumption))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.toUpper; sim'; assumption))
macro_rules | `(tactic| s_misc) => `(tactic| (apply SimE.of_c; simc))

-- Branching values
macro_rules | `(tactic| s_branch) => `(tactic| (apply SimE.cond_ite; simb; sim'; sim'))
macro_rules | `(tactic| s_branch) => `(tactic| (apply SimE.cond_t; simb; known; sim'))
macro_rules | `(tactic| s_branch) => `(tactic| (apply SimE.cond_f; simb; known; sim'))
macro_rules | `(tactic| s_branch) => `(tactic| (apply SimE.or_true; sim'; simb; known))
macro_rules | `(tactic| s_branch) => `(tactic| (apply SimE.or_false; simb; known; sim'))
macro_rules | `(tactic| s_branch) => `(tactic| (apply SimE.and_true; simb; known; sim'))
macro_rules | `(tactic| s_branch) => `(tactic| (apply SimE.and_false; sim'; simb; known))
macro_rules | `(tactic| s_branch) => `(tactic| (apply SimE.coalesce_none; sim'; isnone; sim'))
macro_rules | `(tactic| s_branch) => `(tactic| (apply SimE.coalesce_some; sim_v; infer_instance))
macro_rules | `(tactic| s_misc) => `(tactic| (apply SimE.optField_none; sim'; isnone; simp [nothingOk]))
macro_rules | `(tactic| s_misc) => `(tactic| (apply SimE.array; siml))
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
-- The expression's head picks the rules to try.
open Lean Elab Tactic Meta in
elab "sim0_go" : tactic => withMainContext do
  let t ← whnfR (← instantiateMVars (← (← getMainGoal).getType))
  let e ← whnfR (t.getArg! 2)
  let n := e.getAppFn.constName?.getD .anonymous
  let tac ← match n with
    | ``Expr.var => `(tactic| s_var)
    | ``Expr.lit => `(tactic| s_lit)
    | ``Expr.bin => `(tactic| first | s_bin | s_misc)
    | ``Expr.prim => `(tactic| s_prim)
    | ``Expr.field => `(tactic| s_field)
    | ``Expr.optField => `(tactic| first | s_field | s_misc)
    | ``Expr.record => `(tactic| s_rec)
    | ``Expr.call => `(tactic| s_call)
    | ``Expr.hof => `(tactic| s_hof)
    | ``Expr.reduce => `(tactic| s_hof)
    | ``Expr.cond | ``Expr.or | ``Expr.and | ``Expr.coalesce => `(tactic| first | s_branch | s_misc)
    | _ => `(tactic| s_misc)
  evalTactic tac
macro_rules | `(tactic| sim0) => `(tactic| sim0_go)

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
syntax "c_seqs" : tactic
syntax "c_wend" : tactic
syntax "c_loop_end" : tactic
syntax "l_conj" : tactic
syntax "c_join1" : tactic
syntax "c_join2" : tactic
syntax "c_for" : tactic
syntax "c_while" : tactic
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
    let m := (ty.getArg! 1).consumeMData
    if m.isAppOf ``Aeneas.Std.bind || m.isAppOf ``Bind.bind then
      let n := m.getAppNumArgs
      let inner := (m.getArg! (n - 2)).consumeMData
      let f := (m.getArg! (n - 1)).consumeMData
      return some (inner, if f.isLambda then some f.bindingName! else some Name.anonymous)
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

/-- Reading `xs[i]!` twice gives two names for one value. This keeps the first. -/
elab "dedup_some" : tactic => withMainContext do
  let decls := (← getLCtx).decls.toList.reverse.filterMap id
  let isSomeEq (t : Lean.Expr) : Bool := t.isAppOfArity ``Eq 3 && (t.getArg! 2).isAppOfArity ``Option.some 2
  let mut newest : Option LocalDecl := none
  for d in decls do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOf ``Core.Todo then continue
    if isSomeEq t then newest := some d
    break
  let some n := newest | return
  let tn ← instantiateMVars n.type
  let r := (tn.getArg! 2).getArg! 1
  unless r.isFVar do return
  for d in decls do
    if d.fvarId == n.fvarId || d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if isSomeEq t && t.getArg! 1 == tn.getArg! 1 then
      let e ← mkEqTrans (← mkEqSymm n.toExpr) d.toExpr
      let pf ← mkAppM ``Core.some_inj #[e]
      let g ← getMainGoal
      let (h, g') ← (← g.assert `heq (← inferType pf) pf).intro1P
      let g'' ← Lean.Meta.subst g' h
      replaceMainGoal [g'']
      return

elab "v_step" : tactic => do
  revertTodo
  evalTactic (← `(tactic| with_reducible refine Core.todo_bind ?_))
  evalTactic (← `(tactic| (intro tmp hx hk; first | (revert hx; with_reducible refine Core.ok_intro ?_; intro e; subst e) | (rw [Core.unwrap_iff] at hx; try dedup_some) | skip)))

/-- Reduces the pending step when it matches on a known constructor, as after a loop. -/
def todoReduce : TacticM Unit := withMainContext do
  for d in (← getLCtx).decls.toList.reverse do
    let some d := d | continue
    let ty ← instantiateMVars d.type
    unless ty.isAppOf ``Core.Todo do continue
    let m := (ty.getArg! 1).consumeMData
    if m.getAppFn.isConstOf ``Aeneas.Std.uncurry then
      let some u ← unfoldDefinition? m | return
      let m' ← whnfCore u
      let g ← (← getMainGoal).replaceLocalDeclDefEq d.fvarId (mkAppN ty.getAppFn #[ty.getArg! 0, m', ty.getArg! 2])
      replaceMainGoal [g]
    return

/-- Consumes pure steps up to the end of one source statement. -/
partial def vdrain : TacticM Unit := do
  todoReduce
  let some (m, binder) ← todoHead | return
  if headIs m ``Aeneas.Std.Result.fail then evalTactic (← `(tactic| v_fail)); return
  if binder.isNone then
    if headIs m ``Aeneas.Std.Result.ok then evalTactic (← `(tactic| v_ok))
    return
  if (← isBranch m) || headIs m ``Aeneas.Std.loop then return
  evalTactic (← `(tactic| v_leaf))
  if headIs m ``Aeneas.Std.Result.ok then
    if let some b := binder then
      unless b.toString.startsWith "tmp" || b.isInternal || b.isAnonymous do return
  if (← getGoals).isEmpty then return
  vdrain

elab "vall_go" : tactic => do
  for _ in [0:200] do
    let some (m, binder) ← todoHead | return
    if binder.isNone || (← isBranch m) || headIs m ``Aeneas.Std.loop then return
    evalTactic (← `(tactic| v_leaf))

syntax "c_split" : tactic
syntax "b_set" : tactic
syntax "b_expr" : tactic
syntax "b_ite" : tactic
syntax "b_lock" : tactic
syntax "b_join" : tactic

/-- Runs `a`, keeping nothing if it fails. -/
def attempt (a : TSyntax `tactic) : TacticM Bool := do
  let saved ← Tactic.saveState
  try
    Tactic.withoutRecover (evalTactic a)
    pure true
  catch e =>
    if (← IO.getEnv "BRIDGE_TRACE").isSome then
      IO.eprintln s!"ATTEMPT FAILED {← e.toMessageData.toString}"
    saved.restore
    pure false

/-- Each statement has a first part that can be retried and a rest that can't, so a failure
late in a function doesn't re-explore everything before it. -/
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
  let split ← `(tactic| c_split)
  match kind with
  | `nil =>
    if (t.getArg! 3).isAppOf ``Core.Seq then evalTactic (← `(tactic| c_nil))
    else if (t.getArg! 3).isAppOf ``Core.SeqS then evalTactic (← `(tactic| c_seqs))
    else if (t.getArg! 3).isAppOf ``Core.WEnd' then evalTactic (← `(tactic| c_wend))
    else if branch then evalTactic split
    else if (t.getArg! 3).isAppOf ``Core.LoopQ then evalTactic (← `(tactic| c_loop_end))
    else if (t.getArg! 3).isAppOf ``Core.RetU then evalTactic (← `(tactic| (exact Core.wp_nil ⟨Or.inl rfl, by assumption⟩)))
    else evalTactic (← `(tactic| c_nil))
  | ``Stmt.forOf => evalTactic (← `(tactic| c_for))
  | ``Stmt.whileL => evalTactic (← `(tactic| c_while))
  | ``Stmt.brk => evalTactic (← `(tactic| c_brk))
  | ``Stmt.cont => evalTactic (← `(tactic| c_cont))
  | ``Stmt.throw =>
    if branch then evalTactic split else throwError "STUCK on a throw the typed function doesn't take"
  | ``Stmt.set | ``Stmt.expr | ``Stmt.ret | ``Stmt.ite =>
    if kind == ``Stmt.ite && branch && !tail then
      if ← attempt (← `(tactic| c_join)) then
        evalTactic (← `(tactic| b_join))
        return
    let (first_, rest) ← match kind with
      | ``Stmt.set => pure (← `(tactic| (apply step_set; sim)), ← `(tactic| b_set))
      | ``Stmt.expr => pure (← `(tactic| (apply step_expr; sim)), ← `(tactic| b_expr))
      | ``Stmt.ret => pure (← `(tactic| (apply step_ret; post; assumption; sim)), ← `(tactic| skip))
      | _ =>
        let lock := match pending with
          | some (m, _) => tail && headIs m ``ite
          | none => false
        pure (← `(tactic| (apply step_ite; simb)), ← if lock then `(tactic| b_lock) else `(tactic| b_ite))
    if ← attempt first_ then evalTactic rest; return
    if !tail then
      evalTactic (← `(tactic| vall))
      if ← attempt first_ then evalTactic rest; return
    if (← todoHead).isSome then
      if let some (m, _) ← todoHead then
        if ← isBranch m then evalTactic split; return
    let report ← match kind with
      | ``Stmt.set => `(tactic| (apply step_set; first | sim | fail "STUCK"))
      | ``Stmt.expr => `(tactic| (apply step_expr; first | sim | fail "STUCK"))
      | ``Stmt.ret => `(tactic| (apply step_ret; post; assumption; first | sim | fail "STUCK"))
      | _ => `(tactic| (apply step_ite; first | simb | fail "STUCK"))
    evalTactic report
    throwError "STUCK"
  | n => throwError "STUCK on statement {n}"

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
  evalTactic (← `(tactic| (with_reducible refine Core.todo_ite ?_ ?_) <;> intro hc hk))
elab "v_decide_go" : tactic => do
  revertTodo
  let settled ← attempt (← `(tactic| ((with_reducible refine Core.todo_pos ?_ ?_); assumption)))
  let settled ← if settled then pure true else attempt (← `(tactic| ((with_reducible refine Core.todo_neg ?_ ?_); assumption)))
  let settled ← if settled then pure true else attempt (← `(tactic| ((with_reducible refine Core.todo_pos ?_ ?_); known)))
  let settled ← if settled then pure true else attempt (← `(tactic| ((with_reducible refine Core.todo_neg ?_ ?_); known)))
  if settled then evalTactic (← `(tactic| (intro hk; crun)))
  else evalTactic (← `(tactic| ((with_reducible refine Core.todo_ite ?_ ?_) <;> (intro hc hk; first | (exfalso; refuted) | crun))))
elab "v_split_go" : tactic => do
  revertTodo
  let some (_, _) := some (0, 0) | return
  evalTactic (← `(tactic| first
    | (with_reducible refine Core.todo_bind ?_; intro tmp hx hk; vsplit hx)
    | ((with_reducible refine Core.todo_ite ?_ ?_) <;> intro hc hk)
    | (intro hz; unfold Todo at hz; split at hz <;> (have hk : Todo _ _ := hz; clear hz))))
macro_rules | `(tactic| v_split) => `(tactic| v_split_go)
macro_rules | `(tactic| seq_out) => `(tactic| first | (apply seq_exit; simp; seq_out) | skip)

macro_rules | `(tactic| c_nil) => `(tactic| (apply step_nil; crun))
macro_rules | `(tactic| c_split) => `(tactic| (focus (v_split; all_goals (first | (exfalso; refuted) | crun))))
macro_rules | `(tactic| b_set) => `(tactic| (intro s' hv hk; carry hk; clear hk; crun))
macro_rules | `(tactic| b_expr) => `(tactic| (intro s' hk; carry hk; clear hk; crun))
macro_rules | `(tactic| b_ite) => `(tactic| (
  (focus (intro hp s' hk; first | (exfalso; refuted) | (carry hk; clear hk; crun)))
  (focus (intro hp s' hk; first | (exfalso; refuted) | (carry hk; clear hk; crun)))))
macro_rules | `(tactic| b_lock) => `(tactic| (
  (focus (intro hp s' hk; carry hk; clear hk; v_decide_go))
  (focus (intro hp s' hk; carry hk; clear hk; v_decide_go))))
macro_rules | `(tactic| l_conj) => `(tactic| repeat' (first | trivial | assumption | (apply V.nil_cast; assumption) | apply And.intro))
macro_rules | `(tactic| c_loop_end) => `(tactic| (apply wp_nil; (first | refine ⟨(), rfl, Or.inl rfl, ?_, ?_⟩ | refine ⟨_, rfl, Or.inl rfl, ?_, ?_⟩); assumption; l_conj))
macro_rules | `(tactic| c_brk) => `(tactic| (apply step_brk; seq_out; refine Or.inl ⟨rfl, ?_, ?_⟩; assumption; l_conj))
macro_rules | `(tactic| c_cont) => `(tactic| (apply step_cont; seq_out; first | (show Wp _ _ _ _; crun) | ((first | refine ⟨(), rfl, Or.inr rfl, ?_, ?_⟩ | refine ⟨_, rfl, Or.inr rfl, ?_, ?_⟩); assumption; l_conj)))
macro_rules | `(tactic| c_seqs) => `(tactic| (apply wp_nil; show Wp _ _ _ _; crun))
macro_rules | `(tactic| c_wend) => `(tactic| (apply wp_nil; refine ⟨rfl, _, rfl, Or.inl rfl, ?_, ?_⟩; assumption; l_conj))
elab "v_keep" : tactic => do
  revertTodo
  evalTactic (← `(tactic| with_reducible refine Core.todo_bind ?_))
syntax "j_side" : tactic
macro_rules | `(tactic| c_join1) => `(tactic| (
  v_keep; intro tj hj hk
  apply step_join1 (tj := tj)
  simb
  (focus (intro hp s' he; carry he; clear he; have hj' := Core.ite_pos_of hp hj; vsplit hj'; all_goals sim))
  (focus (intro hp; have hj' := Core.ite_neg_of hp hj; vsplit hj'; all_goals assumption))))
macro_rules | `(tactic| c_join2) => `(tactic| (
  v_keep; intro tj hj hk
  apply step_join (tj := tj)
  simb
  (focus (intro hp s' he; carry he; clear he; have hj' := Core.ite_pos_of hp hj; vsplit hj'; all_goals sim))
  (focus (intro hp s' he; carry he; clear he; have hj' := Core.ite_neg_of hp hj; vsplit hj'; all_goals sim))))
macro_rules | `(tactic| c_join) => `(tactic| first | c_join1 | c_join2)
macro_rules | `(tactic| b_join) => `(tactic| (intro s' hv hu; carry hu; clear hu; crun))

syntax "prog_lookup" : tactic
macro_rules | `(tactic| prog_lookup) => `(tactic| fail "no such function")
macro_rules | `(tactic| s_hof) => `(tactic| fail "no callback rule")
syntax "c_cb" : tactic
open Lean Elab Tactic in
elab "c_cb_t" : tactic => do
  unless ← attempt (← `(tactic| c_cb)) do throwError "STUCK in a callback"
macro_rules | `(tactic| c_cb) => `(tactic| (
  unfold Cb; intro s1 he w a r hw hf
  clear_todo
  carry he; clear he
  apply enter; intro s2 hu he2 hh
  have hv := V.mk' he2 hh hw
  have hb0 := base_of hh
  carry hu; clear hu he2 hh
  beta_reduce at hf
  have hk : Todo _ _ := hf
  clear hf
  crun))
macro_rules | `(tactic| s_hof) => `(tactic| (focus (apply SimE.map; sim'; assumption; (try any_goals infer_instance); prog_lookup; rfl; c_cb_t)))
macro_rules | `(tactic| s_hof) => `(tactic| (focus (apply SimE.filter; sim'; assumption; (try any_goals infer_instance); prog_lookup; rfl; c_cb_t)))
macro_rules | `(tactic| s_hof) => `(tactic| (focus (apply SimE.some_; sim'; assumption; (try any_goals infer_instance); prog_lookup; rfl; c_cb_t)))
macro_rules | `(tactic| s_hof) => `(tactic| (focus (apply SimE.every; sim'; assumption; (try any_goals infer_instance); prog_lookup; rfl; c_cb_t)))
macro_rules | `(tactic| s_hof) => `(tactic| (focus (apply SimE.find; sim'; assumption; (try any_goals infer_instance); prog_lookup; rfl; c_cb_t)))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.append; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.concat_arr; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.replace; sim'; sim'; sim'; assumption))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.replaceAll; sim'; sim'; sim'; assumption))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.substring; sim'; sim'; sim'))
macro_rules | `(tactic| s_prim) => `(tactic| (apply SimE.indexOfStr; sim'; sim'; assumption))
macro_rules | `(tactic| s_misc) => `(tactic| (apply SimE.at_str; sim'; sim'))
macro_rules | `(tactic| sim_read) => `(tactic| (apply SimE.at_str; sim'; sim'))
macro_rules | `(tactic| sim_read) => `(tactic| (apply SimE.at_; sim'; sim'))
syntax "c_cb2" : tactic
open Lean Elab Tactic in
elab "c_cb2_t" : tactic => do
  unless ← attempt (← `(tactic| c_cb2)) do throwError "STUCK in a callback"
macro_rules | `(tactic| c_cb2) => `(tactic| (
  unfold Cb2; intro s1 he u w b a r hu hw hf
  clear_todo
  carry he; clear he
  apply enter2 (by decide); intro s2 s3 hu2 hu3 he2 he3 hh
  have hv1 := V.mk' he2 hh hu
  have hv2 := V.mk' he3 hh hw
  have hb0 := base_of hh
  carry hu2; carry hu3; clear hu2 hu3 he2 he3 hh
  beta_reduce at hf
  have hk : Todo _ _ := hf
  clear hf
  crun))
macro_rules | `(tactic| s_hof) => `(tactic| (focus (apply SimE.reduce; sim'; sim'; assumption; (try any_goals infer_instance); prog_lookup; rfl; c_cb2_t)))

end Core
