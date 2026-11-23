# Proofs about real `number` arithmetic

The functions here work on IEEE-754 binary64 (`NaN`, infinities, `-0`, fractions)
exactly as JavaScript computes them. Each is translated to `Js.Dbl` instead of the
safe-integer `Js.Num`, and the Lean model is `Core.F64` — same bits, same rounding.

## What is proved

- **`totalWithTax` always returns**: `NaN` and `Infinity` are values, not errors,
  so a call can never throw.
- **An exact total, bit for bit**: $12.99 × 2 with 10% off and 20% tax is the
  binary64 nearest $28.06 (`Math.round(… * 100) / 100`).
- **`NaN` propagates**: a `NaN` price makes the total `NaN`.
- **`7.5 % 2 = 1.5`**, bit for bit (JavaScript remainder, sign of the dividend).
- **`effect` answers `NaN` or a whole ±1/±0** for every input.

Statements can talk about bits (`r = Js.Dbl.lit …`, `r.f.isNan`), which prove by
`decide` on concrete inputs, or about values (`Js.Dbl.toRat`, a rational) where an
exact equality holds.
