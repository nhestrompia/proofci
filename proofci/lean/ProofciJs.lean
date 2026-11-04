import Aeneas

/-!
# JavaScript numbers for translated TypeScript

`Js.Num` is a safe integer. Every operation agrees with JavaScript whenever it
succeeds. It fails whenever the exact result is not a safe integer, so a proof
that a function returns a value also proves it never rounded, overflowed or
produced `NaN` or `Infinity`.

The direction matters: `ok v` means JavaScript computes `v`. A failure says
nothing about JavaScript, so code that uses fractions is unproved, never
misjudged. `-0` is treated as `0`: the translator rejects everything that could
tell them apart.

This file declares no axioms.
-/

open Aeneas Aeneas.Std Result

namespace Js

/-- `Number.MAX_SAFE_INTEGER` -/
abbrev MAX : Int := 9007199254740991

structure Num where
  val : Int
  lo : -9007199254740991 ≤ val
  hi : val ≤ 9007199254740991

@[ext] theorem Num.ext {x y : Num} (h : x.val = y.val) : x = y := by
  cases x; cases y; simp_all

instance : DecidableEq Num := fun x y =>
  if h : x.val = y.val then isTrue (Num.ext h) else isFalse (fun e => h (e ▸ rfl))

instance : Repr Num := ⟨fun x _ => repr x.val⟩
instance : Inhabited Num := ⟨⟨0, by decide, by decide⟩⟩

@[scalar_tac x.val]
theorem Num.bounds (x : Num) : -9007199254740991 ≤ x.val ∧ x.val ≤ 9007199254740991 := ⟨x.lo, x.hi⟩

/-- Fails unless `v` is a safe integer. -/
def mk (v : Int) : Result Num :=
  if h : -9007199254740991 ≤ v ∧ v ≤ 9007199254740991 then ok ⟨v, h.1, h.2⟩
  else fail .integerOverflow

def add (x y : Num) : Result Num := mk (x.val + y.val)
def sub (x y : Num) : Result Num := mk (x.val - y.val)
def mul (x y : Num) : Result Num := mk (x.val * y.val)
def neg (x : Num) : Result Num := mk (-x.val)

/-- `x / y`, when the quotient is an integer. -/
def div (x y : Num) : Result Num :=
  if y.val = 0 then fail .divisionByZero
  else if x.val % y.val = 0 then mk (x.val / y.val) else fail .undef

/-- `x % y`. The result takes the sign of `x`, as in JavaScript. -/
def rem (x y : Num) : Result Num :=
  if y.val = 0 then fail .divisionByZero else mk (Int.tmod x.val y.val)

/-- `Math.floor(x / y)`. For safe integers, rounding the double quotient never
    crosses an integer, so the floor is exact. `tests/test_js_numbers.py`
    compares this with Node. -/
def floorDiv (x y : Num) : Result Num :=
  if y.val = 0 then fail .divisionByZero else mk (Int.fdiv x.val y.val)

/-- `Math.ceil(x / y)` -/
def ceilDiv (x y : Num) : Result Num :=
  if y.val = 0 then fail .divisionByZero else mk (-Int.fdiv (-x.val) y.val)

/-- `Math.trunc(x / y)` -/
def truncDiv (x y : Num) : Result Num :=
  if y.val = 0 then fail .divisionByZero else mk (Int.tdiv x.val y.val)

/-- `Math.abs(x)`. Always safe. -/
def abs (x : Num) : Num :=
  ⟨Int.natAbs x.val, by have := x.lo; have := x.hi; omega, by have := x.lo; have := x.hi; omega⟩

/-- `Math.min(x, y)` -/
def min (x y : Num) : Num := if x.val ≤ y.val then x else y

/-- `Math.max(x, y)` -/
def max (x y : Num) : Num := if x.val ≤ y.val then y else x

/-- `x!`. JavaScript would carry on with the null; the model stops, which is the
    safe direction. -/
def unwrap {α} (x : Option α) : Result α :=
  match x with
  | some v => ok v
  | none => fail .undef

theorem mk_spec (v : Int) (h1 : -9007199254740991 ≤ v) (h2 : v ≤ 9007199254740991) :
    mk v ⦃ r => r.val = v ⦄ := by
  simp [mk, h1, h2, WP.spec_ok]

@[step] theorem add_spec (x y : Num)
    (h1 : -9007199254740991 ≤ x.val + y.val) (h2 : x.val + y.val ≤ 9007199254740991) :
    add x y ⦃ r => r.val = x.val + y.val ⦄ := mk_spec _ h1 h2

@[step] theorem sub_spec (x y : Num)
    (h1 : -9007199254740991 ≤ x.val - y.val) (h2 : x.val - y.val ≤ 9007199254740991) :
    sub x y ⦃ r => r.val = x.val - y.val ⦄ := mk_spec _ h1 h2

@[step] theorem mul_spec (x y : Num)
    (h1 : -9007199254740991 ≤ x.val * y.val) (h2 : x.val * y.val ≤ 9007199254740991) :
    mul x y ⦃ r => r.val = x.val * y.val ⦄ := mk_spec _ h1 h2

@[step] theorem neg_spec (x : Num) : neg x ⦃ r => r.val = -x.val ⦄ :=
  mk_spec _ (by have := x.hi; omega) (by have := x.lo; omega)

@[step] theorem floorDiv_spec (x y : Num) (hy : 0 < y.val) :
    floorDiv x y ⦃ r => r.val = x.val / y.val ⦄ := by
  have hy' : y.val ≠ 0 := by omega
  have h : Int.fdiv x.val y.val = x.val / y.val := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ hy.le]
  have hl := x.lo
  have hh := x.hi
  have lower : -9007199254740991 ≤ x.val / y.val :=
    (Int.le_ediv_iff_mul_le hy).mpr (by omega)
  have upper : x.val / y.val < 9007199254740992 :=
    Int.ediv_lt_of_lt_mul hy (by omega)
  simp only [floorDiv, hy', ite_false, h]
  exact mk_spec _ lower (by omega)

@[simp] theorem min_val (x y : Num) : (min x y).val = Min.min x.val y.val := by
  simp only [min]
  split <;> omega

@[simp] theorem max_val (x y : Num) : (max x y).val = Max.max x.val y.val := by
  simp only [max]
  split <;> omega

@[step] theorem unwrap_spec {α} (v : α) : unwrap (some v) ⦃ r => r = v ⦄ := by
  simp [unwrap, WP.spec_ok]

/-- A number for the differential test. Inputs are always safe integers. -/
def lit (v : Int) : Num :=
  if h : -9007199254740991 ≤ v ∧ v ≤ 9007199254740991 then ⟨v, h.1, h.2⟩ else default

/-- Compares the model with what Node computed. `expected` is `none` when Node
    produced something other than a value of the declared type. The model may
    always fail, but when it returns a value, Node must have returned the same. -/
def agree {α} [DecidableEq α] (label : String) (r : Result α) (expected : Option α) : IO Unit :=
  match r.match with
  | .ok v => IO.println (if some v = expected then s!"PROOFCI_DIFF agree {label}" else s!"PROOFCI_DIFF differ {label}")
  | _ => IO.println s!"PROOFCI_DIFF failed {label}"

end Js
