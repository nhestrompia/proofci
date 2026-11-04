import TsBank
open Aeneas Aeneas.Std Result src.ledger

theorem fee_capped (amount rate : Js.Num) (h : amount.val * rate.val ≤ 9007199254740991)
    (h' : -9007199254740991 ≤ amount.val * rate.val) :
    calculateFee amount rate ⦃ fee => fee.val ≤ 500 ⦄ := by
  unfold calculateFee BASIS_POINTS MAX_FEE
  step*
  simp only [Js.min_val]
  omega

theorem transfer_conserves (a : Accounts) (amount : Js.Num)
    (hfrom : 0 ≤ a.from.val) (hto : 0 ≤ a.to.val)
    (htotal : a.from.val + a.to.val ≤ 9007199254740991) :
    transfer a amount ⦃ r => ∀ b, r = some b →
      b.from.val + b.to.val = a.from.val + a.to.val ∧ 0 ≤ b.from.val ⦄ := by
  unfold transfer
  step*

theorem transfer_rejects_overdraft (a : Accounts) (amount : Js.Num) (h : a.from.val < amount.val) :
    transfer a amount = ok none := by
  unfold transfer
  rw [if_pos (Or.inr h)]

theorem sum_exact (xs : List Js.Num) (hn : ∀ x ∈ xs, 0 ≤ x.val)
    (h : Js.total xs ≤ 9007199254740991) :
    sumAmounts xs ⦃ r => r.val = Js.total xs ⦄ := by
  unfold sumAmounts
  apply WP.spec_bind (Pₘ := fun t => t.val = 0) (by simp [WP.spec_ok])
  intro t ht
  apply WP.spec_bind (Pₘ := fun l => l = xs) (by simp [WP.spec_ok])
  intro l hl
  subst hl
  apply WP.spec_bind (Pₘ := fun r => r.val = Js.total l)
  · -- What's left shrinks each step, and the running total plus what's left never changes.
    apply loop.spec_decr_nat (fun s => s.1.length)
      (fun s => 0 ≤ s.2.val ∧ (∀ x ∈ s.1, 0 ≤ x.val) ∧ s.2.val + Js.total s.1 = Js.total l)
    · rintro ⟨rest, t'⟩ ⟨h0, h1, h2⟩
      dsimp only at h0 h1 h2 ⊢
      cases rest with
      | nil =>
        simp only [Js.total_nil] at h2
        simp [WP.spec_ok]
        omega
      | cons x r =>
        simp only [Js.total_cons] at h2
        have hx := h1 x (by simp)
        have hr := Js.total_nonneg r (fun y hy => h1 y (by simp [hy]))
        step*
        simp only [List.length_cons]
        refine ⟨?_, fun y hy => h1 y (by simp [hy]), ?_, ?_⟩ <;> omega
    · dsimp only
      exact ⟨by omega, hn, by omega⟩
  · intro r hr
    simpa [WP.spec_ok] using hr
