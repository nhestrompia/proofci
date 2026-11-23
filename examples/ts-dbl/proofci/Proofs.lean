import TsDbl
open Aeneas Aeneas.Std Result src.pricing

set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem total_always_returns (price quantity discount tax : Js.Dbl) :
    totalWithTax price quantity discount tax ⦃ _ => True ⦄ := by
  unfold totalWithTax
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, WP.spec_ok]
  try (split <;> simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, WP.spec_ok])

theorem menu_price_exact :
    totalWithTax (Js.Dbl.lit 0x4029fae147ae147b) (Js.Dbl.lit 0x4000000000000000)
      (Js.Dbl.lit 0x4024000000000000) (Js.Dbl.lit 0x4034000000000000)
      ⦃ r => r = Js.Dbl.lit 0x403c0f5c28f5c28f ⦄ := by
  have h : totalWithTax (Js.Dbl.lit 0x4029fae147ae147b) (Js.Dbl.lit 0x4000000000000000)
      (Js.Dbl.lit 0x4024000000000000) (Js.Dbl.lit 0x4034000000000000) = ok (Js.Dbl.lit 0x403c0f5c28f5c28f) := by
    unfold totalWithTax
    simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, Js.Dbl.lit]
    decide
  rw [h]
  simp [WP.spec_ok]

theorem nan_propagates (quantity discount tax : Js.Dbl) :
    totalWithTax (Js.Dbl.lit 0x7ff8000000000000) quantity discount tax
      ⦃ r => Js.Dbl.isNaN r = true ⦄ := by
  have hn : Js.Dbl.lit 0x7ff8000000000000 = ⟨Core.F64.nan⟩ := by decide
  rw [hn]
  unfold totalWithTax
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, Js.Dbl.lit, Js.Dbl.isNaN,
    Core.F64.mul, Core.F64.sub, Core.F64.add, Core.F64.div, Core.F64.jsround, Core.F64.isNan,
    WP.spec_ok]
  try (split <;> first | (rename_i h; exact absurd h (by decide)) |
    simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, Js.Dbl.isNaN,
      Core.F64.mul, Core.F64.sub, Core.F64.add, Core.F64.div, Core.F64.jsround, Core.F64.isNan,
      WP.spec_ok])

theorem perHead_exact :
    perHead (Js.Dbl.lit 0x401e000000000000) (Js.Dbl.lit 0x4000000000000000)
      ⦃ r => r = Js.Dbl.lit 0x4008000000000000 ⦄ := by
  have h : perHead (Js.Dbl.lit 0x401e000000000000) (Js.Dbl.lit 0x4000000000000000)
      = ok (Js.Dbl.lit 0x4008000000000000) := by
    unfold perHead
    simp [Js.Dbl.rem, Js.Dbl.sub, Js.Dbl.div, Js.Dbl.lit]
    decide
  rw [h]
  simp [WP.spec_ok]

theorem effect_signs (rate : Js.Dbl) :
    effect rate ⦃ r => r.f.isNan = true ∨ r.f.isInt' = true ⦄ := by
  unfold effect
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.math, Js.Dbl.lit, WP.spec_ok]
  generalize (rate.f.mul rate.f).sub (Core.F64.ofBits 0x3ff0000000000000) = y
  cases y with
  | nan => exact Or.inl rfl
  | inf s => exact Or.inr (by simp [Core.F64.sign, Core.F64.isInt', Nat.mod_self])
  | fin s n =>
    exact Or.inr (by simp [Core.F64.sign]; split <;>
      simp_all [Core.F64.isInt', Nat.zero_mod, Nat.mod_self])
