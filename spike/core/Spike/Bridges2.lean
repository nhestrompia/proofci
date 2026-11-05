import Spike.Step
open Core Aeneas Aeneas.Std Result Gen
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem src_scale_chain320_bridge {h p0 r} (hr : src.scale.chain320 p0 = ok r) :
    WpRun prog src_scale_chain320 [.num (F64.ofInt p0.val)] h fun v s => s.heap = h ∧ Enc.enc s.heap r v := by
  unfold src.scale.chain320 at hr
  try simp (maxSteps := 50000000) only [bind_ok] at hr
  apply wprun
  have va : VarIs ⟨src_scale_chain320.env0 [.num (F64.ofInt p0.val)], h⟩ "a" p0 := by
    have hp : src_scale_chain320.params = ["a"] := rfl
    simp [VarIs, Fn.env0, hp, Env.put]
  have hh : (St.mk (src_scale_chain320.env0 [.num (F64.ofInt p0.val)]) h).heap = h := rfl
  generalize St.mk (src_scale_chain320.env0 [.num (F64.ofInt p0.val)]) h = s0 at va hh
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  split at hr
  · rename_i hc
    have := Result.ok_injective hr; subst this
    exact step_exit_true (SimB.eq_lit (NumE.var va)) hc (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩ rfl
  rename_i hc
  refine step_exit_false (SimB.eq_lit (NumE.var va)) hc ?_
  have := Result.ok_injective hr; subst this
  exact step_ret (NumE.lit _ rfl) ⟨_, rfl, hh, rfl⟩
