import TsDbl
open Aeneas Aeneas.Std Result src.pricing

/-- Every call returns a value: `NaN` and `Infinity` are answers, not errors. -/
theorem total_always_returns (price quantity discount tax : Js.Dbl) :
    totalWithTax price quantity discount tax ⦃ _ => True ⦄ := by sorry

/-- $12.99 for two with a 10% discount and 20% tax is exactly $28.06, bit for bit. -/
theorem menu_price_exact :
    totalWithTax (Js.Dbl.lit 0x4029fae147ae147b) (Js.Dbl.lit 0x4000000000000000)
      (Js.Dbl.lit 0x4024000000000000) (Js.Dbl.lit 0x4034000000000000)
      ⦃ r => r = Js.Dbl.lit 0x403c0f5c28f5c28f ⦄ := by sorry

/-- A `NaN` price makes the total `NaN`. -/
theorem nan_propagates (quantity discount tax : Js.Dbl) :
    totalWithTax (Js.Dbl.lit 0x7ff8000000000000) quantity discount tax
      ⦃ r => Js.Dbl.isNaN r = true ⦄ := by sorry

/-- `7.5 % 2` is `1.5`, bit for bit. -/
theorem leftover_exact :
    leftover (Js.Dbl.lit 0x401e000000000000) (Js.Dbl.lit 0x4000000000000000)
      ⦃ r => r = Js.Dbl.lit 0x3ff8000000000000 ⦄ := by sorry

/-- Whatever the rate, `effect` answers `NaN` or a whole `±1`/`±0`. -/
theorem effect_signs (rate : Js.Dbl) :
    effect rate ⦃ r => r.f.isNan = true ∨ r.f.isInt' = true ⦄ := by sorry
