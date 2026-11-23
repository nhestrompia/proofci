import TsDbl
open Aeneas Aeneas.Std Result src.pricing

/-- A `NaN` price falls into the guard and returns `min` unchanged. -/
theorem shelf_nan (min : Js.Dbl) :
    shelfPrice (Js.Dbl.lit 0x7ff8000000000000) min ⦃ r => r = min ⦄ := by
  sorry

/-- `shelfPrice` covers the double operations the main example does not —
comparisons, `Number.isFinite`/`isNaN`/`isInteger`, `Math.abs`/`min`/`max`/
`trunc`/`ceil`/`floor`, `%` and unary `-` — so a mutant in any of them is
exercised. When it returns a finite value it is non-negative. -/
theorem shelf_nonneg (price min : Js.Dbl) :
    shelfPrice price min ⦃ r => r.f.isFin = true → 0 ≤ Js.Dbl.toRat r ⦄ := by
  sorry
