import Aeneas
open Aeneas Aeneas.Std Result Aeneas.Data.Coinductive Lean.Order

/-! Induction over `loop`, with no termination measure. Aeneas's partial-correctness
judgement treats `fail` as an error, so it can't describe a loop whose body might fail. This
effect semantics allows `fail`, which says only what an `ok` result implies. -/
namespace Core

@[reducible] def failOk : EffectWP RustEffect where
  State := Unit
  wp effect _ _ := match effect with
    | .fail _ => True

instance : EffectWP.Monotonic failOk where
  wp_monotonic := by intro e; cases e; intro _ _ _ _ h; exact h
instance : EffectWP.Conjunctive failOk where
  wp_conj := by intro e; cases e; intros; trivial

unseal Aeneas.Std.Result in
theorem dwlp_bind_any {γ δ : Type} (m : Result γ) (k : γ → Result δ) (Q : δ → Unit → Prop)
    (h : ∀ y, m = ok y → DWLP failOk (k y) Q ()) : DWLP failOk (Aeneas.Std.bind m k) Q () := by
  revert h
  refine Result.cases (motive := fun m => (∀ y, m = ok y → DWLP failOk (k y) Q ()) → DWLP failOk (Aeneas.Std.bind m k) Q ()) m ?_ ?_ ?_
  · intro r h
    simpa using h r rfl
  · intro i k' _
    exact DWLP.bind (Q₁ := fun _ _ => False) (DWLP.vis (by cases i; trivial)) (fun _ _ h => h.elim)
  · intro _
    exact DWLP.bind (Q₁ := fun _ _ => False) DWLP.div (fun _ _ h => h.elim)

unseal Aeneas.Std.Result in
theorem loop_ind {α β : Type} {B : α → Result (ControlFlow α β)} (Q : α → β → Prop)
    (hstep : ∀ a y, B a = ok y → match y with
      | .done r => Q a r
      | .cont a' => ∀ r, Q a' r → Q a r) :
    ∀ a r, loop B a = ok r → Q a r := by
  have key : ∀ a, DWLP failOk (loop B a) (fun v _ => Q a v) () := by
    apply loop.fixpoint_induct B (fun f => ∀ a, DWLP failOk (f a) (fun v _ => Q a v) ())
    · apply admissible_pi
      intro a
      exact admissible_apply (fun _ m => DWLP failOk m (fun v _ => Q a v) ()) a (DWLP.admissible failOk _ ())
    · intro f ih a
      refine dwlp_bind_any _ _ _ fun y hy => ?_
      cases y with
      | cont a' => exact (ih a').mono fun v _ h => hstep a (.cont a') hy v h
      | done r => exact DWLP.ret_iff.mpr (hstep a (.done r) hy)
  intro a r h
  have := key a
  rw [h] at this
  exact DWLP.ret_iff.mp this

end Core
