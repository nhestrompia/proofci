import TsAssumes
open Aeneas Aeneas.Std Result src.label

theorem label_tagged (title : Js.Str)
    (slug_nonempty : ∃ s, Proofci.Assumed.slug_maker.slug title = ok s ∧ s ≠ []) :
    label title ⦃ r => r.head? = some 35 ∧ 2 ≤ r.length ⦄ := by
  obtain ⟨s, hs, hne⟩ := slug_nonempty
  unfold label
  rw [hs]
  cases s with
  | nil => exact absurd rfl hne
  | cons c cs => simp [WP.spec_ok] <;> omega
