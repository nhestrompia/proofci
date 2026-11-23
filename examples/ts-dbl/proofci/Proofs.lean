import TsDbl
open Aeneas Aeneas.Std Result src.pricing

theorem total_always_returns (price quantity discount tax : Js.Dbl) :
    totalWithTax price quantity discount tax ⦃ _ => True ⦄ := by
  unfold totalWithTax
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, WP.spec_ok]

theorem menu_price_exact :
    totalWithTax (Js.Dbl.lit 0x4029fae147ae147b) (Js.Dbl.lit 0x4000000000000000)
      (Js.Dbl.lit 0x4024000000000000) (Js.Dbl.lit 0x4034000000000000)
      ⦃ r => r = Js.Dbl.lit 0x403c0f5c28f5c28f ⦄ := by
  have h : totalWithTax (Js.Dbl.lit 0x4029fae147ae147b) (Js.Dbl.lit 0x4000000000000000)
      (Js.Dbl.lit 0x4024000000000000) (Js.Dbl.lit 0x4034000000000000) = ok (Js.Dbl.lit 0x403c0f5c28f5c28f) := by
    decide
  rw [h]
  simp [WP.spec_ok]

theorem nan_propagates (quantity discount tax : Js.Dbl) :
    totalWithTax (Js.Dbl.lit 0x7ff8000000000000) quantity discount tax
      ⦃ r => Js.Dbl.isNaN r = true ⦄ := by
  have hn : Js.Dbl.lit 0x7ff8000000000000 = ⟨Core.F64.nan⟩ := by decide
  rw [hn]
  unfold totalWithTax
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, Js.Dbl.isNaN,
    Core.F64.mul, Core.F64.sub, Core.F64.add, Core.F64.div, Core.F64.jsround, WP.spec_ok]

theorem leftover_exact :
    leftover (Js.Dbl.lit 0x401e000000000000) (Js.Dbl.lit 0x4000000000000000)
      ⦃ r => r = Js.Dbl.lit 0x3ff8000000000000 ⦄ := by
  have h : leftover (Js.Dbl.lit 0x401e000000000000) (Js.Dbl.lit 0x4000000000000000)
      = ok (Js.Dbl.lit 0x3ff8000000000000) := by
    decide
  rw [h]
  simp [WP.spec_ok]

theorem effect_signs (rate : Js.Dbl) :
    effect rate ⦃ r => r.f.isNan = true ∨ r.f.isInt' = true ⦄ := by
  unfold effect
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.math, WP.spec_ok]
  generalize (rate.f.mul rate.f).sub (Core.F64.ofBits 0x3ff0000000000000) = y
  cases y with
  | nan => exact Or.inl rfl
  | inf s => exact Or.inr (by simp [Core.F64.sign, Core.F64.isInt', Core.F64.unit])
  | fin s n =>
    exact Or.inr (by simp [Core.F64.sign]; split <;> simp [Core.F64.isInt', Core.F64.unit])
