import TsDbl
open Aeneas Aeneas.Std Result src.pricing

/-- `totalWithTax` on finite, non-negative, realistically bounded inputs
(`price, quantity ≤ 10⁹`, `discount ≤ 100`, `tax ≤ 1000`) always returns a
finite non-negative value: no intermediate can overflow to `Infinity` or turn
`NaN`. Bounds are stated on `Js.Dbl.toRat`, the real value view, so no
bit-level reasoning appears in the contract. -/
theorem total_nonneg (price quantity discount tax : Js.Dbl)
    (hpf : price.f.isFin = true) (hqf : quantity.f.isFin = true)
    (hdf : discount.f.isFin = true) (htf : tax.f.isFin = true)
    (hp : 0 ≤ Js.Dbl.toRat price) (hpB : Js.Dbl.toRat price ≤ 10 ^ 9)
    (hq : 0 ≤ Js.Dbl.toRat quantity) (hqB : Js.Dbl.toRat quantity ≤ 10 ^ 9)
    (hd : 0 ≤ Js.Dbl.toRat discount) (hd100 : Js.Dbl.toRat discount ≤ 100)
    (ht : 0 ≤ Js.Dbl.toRat tax) (htB : Js.Dbl.toRat tax ≤ 1000) :
    totalWithTax price quantity discount tax
      ⦃ r => r.f.isFin = true ∧ 0 ≤ Js.Dbl.toRat r ⦄ := by
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

/-- `perHead` on a finite non-negative `total ≤ 10⁹` split `parts ≥ 1` ways
returns a finite non-negative share: `%` stays below the total and the
division cannot overflow. -/
theorem perHead_nonneg (total parts : Js.Dbl)
    (htf : total.f.isFin = true) (hpf : parts.f.isFin = true)
    (ht : 0 ≤ Js.Dbl.toRat total) (htB : Js.Dbl.toRat total ≤ 10 ^ 9)
    (hp : 1 ≤ Js.Dbl.toRat parts) :
    perHead total parts ⦃ r => r.f.isFin = true ∧ 0 ≤ Js.Dbl.toRat r ⦄ := by
  sorry

/-- Whatever the rate, `effect` answers `NaN` or a whole `±1`/`±0`. -/
theorem effect_signs (rate : Js.Dbl) :
    effect rate ⦃ r => r.f.isNan = true ∨ r.f.isInt' = true ⦄ := by
  sorry
