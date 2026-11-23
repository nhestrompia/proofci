import TsDbl
open Aeneas Aeneas.Std Result src.pricing

/-- `totalWithTax` on finite non-negative inputs with a bounded discount stays
non-negative: price, quantity and tax only round a non-negative subtotal, the
discount multiplier lies in `[0, 1]` and `Math.round` never turns a
non-negative number negative. Bounds are stated on `Js.Dbl.toRat`, the real
value view, so no bit-level reasoning appears in the contract. -/
theorem total_nonneg (price quantity discount tax : Js.Dbl)
    (hp : 0 ≤ Js.Dbl.toRat price) (hq : 0 ≤ Js.Dbl.toRat quantity)
    (hd : 0 ≤ Js.Dbl.toRat discount) (hd100 : Js.Dbl.toRat discount ≤ 100)
    (ht : 0 ≤ Js.Dbl.toRat tax) :
    totalWithTax price quantity discount tax ⦃ r => 0 ≤ Js.Dbl.toRat r ⦄ := by
  sorry

/-- Whenever the total comes out finite it is a whole number of cents: it is a
quotient of an integer-valued binary64 over `100`. `isInteger` is phrased with
`toRatD`/`isInt'`, the value view `Js.Dbl.toRat` is built on. -/
theorem whole_cents (price quantity discount tax : Js.Dbl) :
    totalWithTax price quantity discount tax
      ⦃ r => r.f.isFin = true →
        ∃ k : Int, ∃ z : Core.F64,
          r.f = z.div (Core.F64.ofInt 100) ∧ z.toRatD = k ⦄ := by
  sorry

/-- $12.99 for two with a 10% discount and 20% tax is exactly $28.06, bit for
bit. `dbl!"…"` literals read as decimals but compile to the nearest binary64. -/
theorem menu_price_exact :
    totalWithTax (dbl!"12.99") (dbl!"2") (dbl!"10") (dbl!"20")
      ⦃ r => r = dbl!"28.06" ⦄ := by
  sorry

/-- A `NaN` price makes the total `NaN`. -/
theorem nan_propagates (quantity discount tax : Js.Dbl) :
    totalWithTax (Js.Dbl.lit 0x7ff8000000000000) quantity discount tax
      ⦃ r => Js.Dbl.isNaN r = true ⦄ := by
  sorry

/-- `perHead` on non-negative inputs returns a non-negative value: `%` stays
below the total and `/` of non-negatives is non-negative. -/
theorem perHead_nonneg (total parts : Js.Dbl)
    (ht : 0 ≤ Js.Dbl.toRat total) (hp : 0 ≤ Js.Dbl.toRat parts) :
    perHead total parts ⦃ r => 0 ≤ Js.Dbl.toRat r ⦄ := by
  sorry

/-- Whatever the rate, `effect` answers `NaN` or a whole `±1`/`±0`. -/
theorem effect_signs (rate : Js.Dbl) :
    effect rate ⦃ r => r.f.isNan = true ∨ r.f.isInt' = true ⦄ := by
  sorry

/-- `shelfPrice` exists to cover the remaining double operations — comparisons,
`Number.isFinite`/`isNaN`/`isInteger`, `Math.abs`/`min`/`max`/`trunc`/`ceil`/
`floor`, `%` and unary `-` — so a mutant in any of them is exercised. When it
returns a finite value it is non-negative. -/
theorem shelf_nonneg (price min : Js.Dbl) :
    shelfPrice price min ⦃ r => r.f.isFin = true → 0 ≤ Js.Dbl.toRat r ⦄ := by
  sorry

/-- `bonus` reads the computed integer constant `freeUnits` through
`Js.Dbl.ofNumNe`, which refuses `0` — so the view fails and the postcondition is
vacuous. The function stays `tested` on every input. -/
theorem bonus_nonneg (price : Js.Dbl) :
    bonus price ⦃ r => r.f.isFin = true → 0 ≤ Js.Dbl.toRat r ⦄ := by
  sorry
