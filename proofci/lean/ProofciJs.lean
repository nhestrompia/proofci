import Aeneas
import F64

/-!
# JavaScript numbers for translated TypeScript

`Js.Num` is a safe integer. Every operation agrees with JavaScript whenever it
succeeds. It fails whenever the exact result is not a safe integer, so a proof
that a function returns a value also proves it never rounded, overflowed or
produced `NaN` or `Infinity`.

`Js.Dbl` is a full IEEE-754 binary64 (`Core.F64`): fractions, `NaN`, `Infinity`
and `-0` exactly as JavaScript computes them. It is the sibling of `Js.Num` for
functions that work on prices, percentages, averages or ratios. `ok` means the
same thing for both: JavaScript computes that value.

The direction matters: `ok v` means JavaScript computes `v`. A failure says
nothing about JavaScript, so code that uses unmodelled forms is unproved, never
misjudged.

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

/-- Lets `scalar_tac` see through number literals in translated code. -/
@[simp, scalar_tac_simps] theorem Num.val_mk (v : Int) (a : -9007199254740991 ≤ v) (b : v ≤ 9007199254740991) :
    (Num.mk v a b).val = v := rfl

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

/-- `xs.filter((x): x is T => ...)`: the type says every kept value is present. -/
def unwrapAll {α} : List (Option α) → Result (List α)
  | [] => ok []
  | x :: rest => do
    let v ← unwrap x
    let vs ← unwrapAll rest
    ok (v :: vs)

/-- `if (x)` on a possibly missing value. A present value can still be falsy. -/
def truthyStr : Option (List Nat) → Bool
  | some s => !s.isEmpty
  | none => false
def truthyNum : Option Num → Bool
  | some n => n.val != 0
  | none => false
def truthyBool : Option Bool → Bool
  | some b => b
  | none => false
def truthyBig : Option Int → Bool
  | some n => n != 0
  | none => false


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

/-- `x % y` for a positive divisor: Lean's `Int.tmod`, which truncates toward zero like JavaScript. -/
@[step] theorem rem_spec (x y : Num) (hy : 0 < y.val) :
    rem x y ⦃ r => r.val = Int.tmod x.val y.val ⦄ := by
  have hy' : y.val ≠ 0 := by omega
  have h1 := Int.tmod_lt_of_pos x.val hy
  have h2 := Int.lt_tmod_of_pos x.val hy
  have := y.hi
  simp only [rem, hy', ite_false]
  exact mk_spec _ (by omega) (by omega)

@[step] theorem truncDiv_spec (x y : Num) (hy : y.val ≠ 0) :
    truncDiv x y ⦃ r => r.val = x.val.tdiv y.val ⦄ := by
  simp only [truncDiv, ite_eq_right hy]
  have hb : (x.val.tdiv y.val).natAbs ≤ x.val.natAbs := Int.natAbs_tdiv_le_natAbs _ _
  exact mk_spec _ (by have := x.lo; have := x.hi; omega) (by have := x.lo; have := x.hi; omega)

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

/-- `a / b` on `bigint`: truncates, and throws on zero. -/
def bdiv (a b : Int) : Result Int := if b = 0 then fail .panic else ok (Int.tdiv a b)

/-- `a % b` on `bigint`: takes the sign of `a`, and throws on zero. -/
def brem (a b : Int) : Result Int := if b = 0 then fail .panic else ok (Int.tmod a b)

@[step] theorem bdiv_spec (a b : Int) (h : b ≠ 0) : bdiv a b ⦃ r => r = Int.tdiv a b ⦄ := by
  simp [bdiv, h, WP.spec_ok]

@[step] theorem brem_spec (a b : Int) (h : b ≠ 0) : brem a b ⦃ r => r = Int.tmod a b ⦄ := by
  simp [brem, h, WP.spec_ok]

/-- `try { body } catch { handler }`. `.panic` is only produced by `throw`, so
    the handler runs for exceptions and never for leaving the model. -/
def attempt {α} (body handler : Result α) : Result α :=
  match body.match with
  | .vis (.fail .panic) _ => handler
  | _ => body

@[simp] theorem attempt_ok {α} (v : α) (h : Result α) : attempt (ok v) h = ok v := by
  simp [attempt]

@[simp] theorem attempt_panic {α} (h : Result α) : attempt (fail .panic) h = h := by
  simp [attempt]

/-! ## Step lemmas for emitted code

The view emits `do`-notation that elaborates to `Bind.bind` (the `>>=` class
projection), not `Aeneas.Std.bind`. `step` recognizes both, and `bind_tc_eq`
lets `simp` normalize one into the other; `spec_bind'` is `spec_bind` stated on
the emitted form for manual proofs. -/

theorem spec_bind' {α β : Type _} {k : α → Result β} {Pₖ : WP.Post β} {m : Result α} {Pₘ : WP.Post α} :
    WP.spec m Pₘ → (∀ x, Pₘ x → WP.spec (k x) Pₖ) → WP.spec (Bind.bind m k) Pₖ := WP.spec_bind

/-- `let x ← if c then a else b …`: the step_simps normalizer pushes the bind
    inside the branches, so `step*` leaves one goal per branch. -/
@[simp, step_simps] theorem bind_tc_ite {α β : Type _} {c : Prop} [Decidable c]
    (a b : Result α) (f : α → Result β) :
    Bind.bind (if c then a else b) f = if c then Bind.bind a f else Bind.bind b f := by
  by_cases h : c <;> simp [h]

/-- `Std.bind` version of `bind_tc_ite`: `do`-blocks elaborate to `Bind.bind`
    while library code uses `Aeneas.Std.bind`, so both forms get a pushing lemma. -/
@[simp] theorem bind_ite {α β : Type _} {c : Prop} [Decidable c]
    (a b : Result α) (f : α → Result β) :
    Std.bind (if c then a else b) f = if c then Std.bind a f else Std.bind b f := by
  by_cases h : c <;> simp [h]

/-- `let x ← if c then a else b …`: split the condition at bind position. Both
    branches keep the same postcondition. Not tagged `@[step]`: tagging it makes
    `step*` create a shared-post metavariable goal that stalls proofs. Push the
    bind under the `if` with `bind_tc_ite`/`bind_ite` and use `split` instead. -/
theorem spec_ite {α : Type _} {c : Prop} [Decidable c] {a b : Result α} {post : WP.Post α}
    (h₁ : c → WP.spec a post) (h₂ : ¬c → WP.spec b post) :
    WP.spec (if c then a else b) post := by
  by_cases h : c
  · simpa [h] using h₁ h
  · simpa [h] using h₂ h

/-- Inverting a `Bind.bind` equation on the emitted form, for manual proofs. -/
theorem bind_tc_inv {α β : Type _} {x : Result α} {f : α → Result β} {r : β}
    (h : Bind.bind x f = ok r) : ∃ a, x = ok a ∧ f a = ok r := by
  revert h
  refine Result.cases (motive := fun x => Bind.bind x f = ok r → ∃ a, x = ok a ∧ f a = ok r) x ?_ ?_ ?_
  · intro a h; exact ⟨a, rfl, by simpa using h⟩
  · intro i k h; simp at h
  · intro h; simp at h

/-! ## Arrays

An array is a `List`. Translated code never shares one between two names while
changing it: the translator's ownership check rejects that, so a value is enough. -/

/-- `xs.length` -/
def len {α} (xs : List α) : Result Num := mk xs.length

/-- `xs[i]`. A negative or out-of-range index reads `undefined`. -/
def at_ {α} (xs : List α) (i : Num) : Option α :=
  if i.val < 0 then none else xs[i.val.toNat]?

/-- `xs[i] = v` for an index inside the array. Writing past the end would make
    holes, so the model stops there. -/
def setAt {α} (xs : List α) (i : Num) (v : α) : Result (List α) :=
  if 0 ≤ i.val ∧ i.val < xs.length then ok (xs.set i.val.toNat v) else fail .undef

/-- A `slice` bound: negative counts from the end, and it is clamped to the array. -/
def bound (n : Nat) (i : Num) : Nat :=
  if i.val < 0 then (Max.max (n + i.val) 0).toNat else Min.min i.val.toNat n

/-- `xs.slice(a, b)` -/
def slice {α} (xs : List α) (a b : Num) : List α :=
  let from_ := bound xs.length a
  (xs.take (bound xs.length b)).drop from_

/-- `xs.slice(a)` -/
def sliceFrom {α} (xs : List α) (a : Num) : List α := xs.drop (bound xs.length a)

/-- `xs.includes(v)`, for values compared by value. -/
def includes {α} [DecidableEq α] (xs : List α) (v : α) : Bool := xs.contains v

/-- `xs.indexOf(v)`, for values compared by value. -/
def indexOf {α} [DecidableEq α] (xs : List α) (v : α) : Result Num :=
  match xs.idxOf? v with
  | some i => mk i
  | none => mk (-1)

def map {α β} (f : α → Result β) : List α → Result (List β)
  | [] => ok []
  | x :: rest => do
    let y ← f x
    let ys ← map f rest
    ok (y :: ys)

def filter {α} (f : α → Result Bool) : List α → Result (List α)
  | [] => ok []
  | x :: rest => do
    let keep ← f x
    let ys ← filter f rest
    ok (if keep then x :: ys else ys)

def some_ {α} (f : α → Result Bool) : List α → Result Bool
  | [] => ok false
  | x :: rest => do
    let hit ← f x
    if hit then ok true else some_ f rest

def every {α} (f : α → Result Bool) : List α → Result Bool
  | [] => ok true
  | x :: rest => do
    let hit ← f x
    if hit then every f rest else ok false

def find {α} (f : α → Result Bool) : List α → Result (Option α)
  | [] => ok none
  | x :: rest => do
    let hit ← f x
    if hit then ok (some x) else find f rest

def reduce {α β} (f : β → α → Result β) (acc : β) : List α → Result β
  | [] => ok acc
  | x :: rest => do
    let next ← f acc x
    reduce f next rest

section Monotone
open Lean.Order

-- A recursive function that calls itself inside a callback is still a `partial_fixpoint`.
@[partial_fixpoint_monotone]
theorem monotone_map {γ : Type} [Lean.Order.PartialOrder γ] {α β} (f : γ → α → Result β) (xs : List α)
    (hmono : monotone f) : monotone (fun x => map (f x) xs) := by
  induction xs with
  | nil => simp only [map]; apply Lean.Order.monotone_const
  | cons x rest ih =>
    simp only [map]
    apply Aeneas.Std.bind_mono
    · exact Lean.Order.monotone_apply x f hmono
    · apply Lean.Order.monotone_of_monotone_apply; intro y
      apply Aeneas.Std.bind_mono
      · exact ih
      · apply Lean.Order.monotone_const

@[partial_fixpoint_monotone]
theorem monotone_filter {γ : Type} [Lean.Order.PartialOrder γ] {α} (f : γ → α → Result Bool) (xs : List α)
    (hmono : monotone f) : monotone (fun x => filter (f x) xs) := by
  induction xs with
  | nil => simp only [filter]; apply Lean.Order.monotone_const
  | cons x rest ih =>
    simp only [filter]
    apply Aeneas.Std.bind_mono
    · exact Lean.Order.monotone_apply x f hmono
    · apply Lean.Order.monotone_of_monotone_apply; intro y
      apply Aeneas.Std.bind_mono
      · exact ih
      · apply Lean.Order.monotone_const

@[partial_fixpoint_monotone]
theorem monotone_some_ {γ : Type} [Lean.Order.PartialOrder γ] {α} (f : γ → α → Result Bool) (xs : List α)
    (hmono : monotone f) : monotone (fun x => some_ (f x) xs) := by
  induction xs with
  | nil => simp only [some_]; apply Lean.Order.monotone_const
  | cons x rest ih =>
    simp only [some_]
    apply Aeneas.Std.bind_mono
    · exact Lean.Order.monotone_apply x f hmono
    · apply Lean.Order.monotone_of_monotone_apply; intro y
      apply Lean.Order.monotone_ite
      · apply Lean.Order.monotone_const
      · exact ih

@[partial_fixpoint_monotone]
theorem monotone_every {γ : Type} [Lean.Order.PartialOrder γ] {α} (f : γ → α → Result Bool) (xs : List α)
    (hmono : monotone f) : monotone (fun x => every (f x) xs) := by
  induction xs with
  | nil => simp only [every]; apply Lean.Order.monotone_const
  | cons x rest ih =>
    simp only [every]
    apply Aeneas.Std.bind_mono
    · exact Lean.Order.monotone_apply x f hmono
    · apply Lean.Order.monotone_of_monotone_apply; intro y
      apply Lean.Order.monotone_ite
      · exact ih
      · apply Lean.Order.monotone_const

@[partial_fixpoint_monotone]
theorem monotone_find {γ : Type} [Lean.Order.PartialOrder γ] {α} (f : γ → α → Result Bool) (xs : List α)
    (hmono : monotone f) : monotone (fun x => find (f x) xs) := by
  induction xs with
  | nil => simp only [find]; apply Lean.Order.monotone_const
  | cons x rest ih =>
    simp only [find]
    apply Aeneas.Std.bind_mono
    · exact Lean.Order.monotone_apply x f hmono
    · apply Lean.Order.monotone_of_monotone_apply; intro y
      apply Lean.Order.monotone_ite
      · apply Lean.Order.monotone_const
      · exact ih

@[partial_fixpoint_monotone]
theorem monotone_reduce {γ : Type} [Lean.Order.PartialOrder γ] {α β} (f : γ → β → α → Result β) (acc : β)
    (xs : List α) (hmono : monotone f) : monotone (fun x => reduce (f x) acc xs) := by
  induction xs generalizing acc with
  | nil => simp only [reduce]; apply Lean.Order.monotone_const
  | cons x rest ih =>
    simp only [reduce]
    apply Aeneas.Std.bind_mono
    · exact Lean.Order.monotone_apply x _ (Lean.Order.monotone_apply acc f hmono)
    · apply Lean.Order.monotone_of_monotone_apply; intro y
      exact ih y

end Monotone

@[simp] theorem map_nil {α β} (f : α → Result β) : map f [] = ok [] := rfl
@[simp] theorem filter_nil {α} (f : α → Result Bool) : filter f [] = ok [] := rfl

/-- Every element `filter` keeps when its predicate always succeeds
    was already in the list it read. -/
theorem spec_filter_mem {α} (g : α → Bool) (xs : List α) :
    WP.spec (filter (fun x => ok (g x)) xs) (fun r => ∀ y ∈ r, y ∈ xs) := by
  induction xs with
  | nil =>
    simp only [filter, WP.spec_ok]
    intro y hy
    exact hy
  | cons x rest ih =>
    simp only [filter]
    apply WP.spec_bind
      (Pₘ := fun (keep : Bool) =>
        WP.spec (Aeneas.Std.bind (filter (fun x => ok (g x)) rest)
          (fun ys => ok (if keep then x :: ys else ys)))
          (fun r => ∀ y ∈ r, y ∈ x :: rest))
    · rw [WP.spec_ok]
      apply WP.spec_bind (Pₘ := fun ys => ∀ y ∈ (if g x then x :: ys else ys), y ∈ x :: rest)
      · apply WP.spec_mono ih
        intro ys ihys y hy
        simp only [List.mem_cons]
        cases hgc : g x <;> simp [hgc, List.mem_cons] at hy
        · exact Or.inr (ihys y hy)
        · cases hy with
          | inl e => exact Or.inl e
          | inr hmem => exact Or.inr (ihys y hmem)
      · intro ys ihys
        rw [WP.spec_ok]
        exact ihys
    · intro keep h
      exact h

@[simp] theorem reduce_nil {α β} (f : β → α → Result β) (acc : β) : reduce f acc [] = ok acc := rfl

/-! Equational forms for the higher-order combinators. The premise is
    per-element (`∀ x, f x = ok (g x)`), so a proof can rewrite the callback
    pointwise — `intro x; simp [cb]` — instead of proving a function equality
    with `funext` on the emitted `do`-block lambda. -/

theorem map_eq {α β} {f : α → Result β} {g : α → β}
    (hf : ∀ x, f x = ok (g x)) : ∀ xs : List α, map f xs = ok (xs.map g) := by
  intro xs; induction xs with
  | nil => rfl
  | cons x rest ih => simp only [map, hf x, ih, Std.bind_ok, List.map_cons]

@[step] theorem map_spec {α β} {f : α → Result β} {g : α → β} {xs : List α}
    (hf : ∀ x, f x = ok (g x)) : map f xs ⦃ ys => ys = xs.map g ⦄ := by
  rw [map_eq hf]; simp [WP.spec_ok]

theorem filter_eq {α} {f : α → Result Bool} {p : α → Bool}
    (hf : ∀ x, f x = ok (p x)) : ∀ xs : List α, filter f xs = ok (xs.filter p) := by
  intro xs; induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases h : p x <;> simp [filter, hf x, ih, Std.bind_ok, h]

@[step] theorem filter_spec {α} {f : α → Result Bool} {p : α → Bool} {xs : List α}
    (hf : ∀ x, f x = ok (p x)) : filter f xs ⦃ ys => ys = xs.filter p ⦄ := by
  rw [filter_eq hf]; simp [WP.spec_ok]

theorem some_eq {α} {f : α → Result Bool} {p : α → Bool}
    (hf : ∀ x, f x = ok (p x)) : ∀ xs : List α, some_ f xs = ok (xs.any p) := by
  intro xs; induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases h : p x <;> simp [some_, hf x, ih, Std.bind_ok, h]

@[step] theorem some_spec {α} {f : α → Result Bool} {p : α → Bool} {xs : List α}
    (hf : ∀ x, f x = ok (p x)) : some_ f xs ⦃ r => r = xs.any p ⦄ := by
  rw [some_eq hf]; simp [WP.spec_ok]

theorem every_eq {α} {f : α → Result Bool} {p : α → Bool}
    (hf : ∀ x, f x = ok (p x)) : ∀ xs : List α, every f xs = ok (xs.all p) := by
  intro xs; induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases h : p x <;> simp [every, hf x, ih, Std.bind_ok, h]

@[step] theorem every_spec {α} {f : α → Result Bool} {p : α → Bool} {xs : List α}
    (hf : ∀ x, f x = ok (p x)) : every f xs ⦃ r => r = xs.all p ⦄ := by
  rw [every_eq hf]; simp [WP.spec_ok]

theorem find_eq {α} {f : α → Result Bool} {p : α → Bool}
    (hf : ∀ x, f x = ok (p x)) : ∀ xs : List α, find f xs = ok (xs.find? p) := by
  intro xs; induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases h : p x <;> simp [find, hf x, ih, Std.bind_ok, h]

@[step] theorem find_spec {α} {f : α → Result Bool} {p : α → Bool} {xs : List α}
    (hf : ∀ x, f x = ok (p x)) : find f xs ⦃ r => r = xs.find? p ⦄ := by
  rw [find_eq hf]; simp [WP.spec_ok]

/-- Folding a function that ignores its argument returns the accumulator. -/
@[simp] theorem foldl_const {α β : Type _} (acc : β) (xs : List α) :
    xs.foldl (fun a _ => a) acc = acc := by
  induction xs generalizing acc <;> simp_all [List.foldl]

theorem reduce_eq {α β} {f : β → α → Result β} {g : β → α → β}
    (hf : ∀ a x, f a x = ok (g a x)) : ∀ (acc : β) (xs : List α), reduce f acc xs = ok (xs.foldl g acc) := by
  intro acc xs; induction xs generalizing acc with
  | nil => rfl
  | cons x rest ih =>
    simp only [reduce, hf acc x, ih (g acc x), Std.bind_ok, List.foldl_cons]

@[step] theorem reduce_spec {α β} {f : β → α → Result β} {g : β → α → β} {acc : β} {xs : List α}
    (hf : ∀ a x, f a x = ok (g a x)) : reduce f acc xs ⦃ r => r = xs.foldl g acc ⦄ := by
  rw [reduce_eq hf]; simp [WP.spec_ok]

/-- The fold-invariant form of `reduce`: when every step preserves `inv`, the
    result satisfies `inv`. This is the loop-invariant pattern for folds. -/
@[step] theorem reduce_spec_inv {α β} {f : β → α → Result β} {inv : β → Prop}
    {acc : β} {xs : List α}
    (h0 : inv acc) (hf : ∀ a x, inv a → f a x ⦃ r => inv r ⦄) :
    reduce f acc xs ⦃ r => inv r ⦄ := by
  induction xs generalizing acc with
  | nil => simpa [reduce] using h0
  | cons x rest ih =>
    simp only [reduce]
    apply spec_bind' (hf acc x h0)
    intro next hn
    exact ih hn

/-- `xs.includes(v)` is `xs.contains v`: the spec version needs nothing more. -/
@[simp] theorem includes_eq {α} [DecidableEq α] (xs : List α) (v : α) :
    includes xs v = xs.contains v := rfl

@[simp] theorem includes_iff {α} [DecidableEq α] (xs : List α) (v : α) :
    includes xs v = true ↔ v ∈ xs := by simp [includes]

/-- `s.indexOf(v)`: `some` position or `-1`. -/
@[step] theorem indexOf_val {α} [DecidableEq α] (xs : List α) (v : α)
    (hl : xs.length ≤ 9007199254740991) :
    indexOf xs v ⦃ r => r.val = match xs.idxOf? v with | some i => (i : Int) | none => -1 ⦄ := by
  simp only [indexOf]
  cases h : xs.idxOf? v with
  | some i =>
    obtain ⟨hlt, -, -⟩ := List.idxOf?_eq_some_iff.mp h
    exact mk_spec _ (by omega) (by omega)
  | none => exact mk_spec _ (by omega) (by omega)

/-- A `slice` bound never exceeds the array length. -/
theorem bound_le (n : Nat) (i : Num) : bound n i ≤ n := by
  simp only [bound]
  split <;> omega

/-- `xs.slice(a, b)` stays within `xs`. -/
theorem slice_length_le {α} (xs : List α) (a b : Num) : (slice xs a b).length ≤ xs.length := by
  simp only [slice, List.length_drop, List.length_take]
  have hb := bound_le xs.length b
  omega

theorem slice_mem {α} (xs : List α) (a b : Num) {y : α} (h : y ∈ slice xs a b) : y ∈ xs :=
  List.mem_of_mem_take (List.mem_of_mem_drop h)

/-- `xs.slice(a)` stays within `xs`. -/
theorem sliceFrom_length_le {α} (xs : List α) (a : Num) : (sliceFrom xs a).length ≤ xs.length := by
  simp only [sliceFrom, List.length_drop]; omega

@[step] theorem len_spec {α} (xs : List α) (h : xs.length ≤ 9007199254740991) :
    len xs ⦃ r => r.val = xs.length ⦄ :=
  mk_spec _ (by omega) (by omega)

/-- The exact total of a list of numbers, for stating what a sum computes. -/
def total (xs : List Num) : Int := (xs.map (·.val)).sum

@[simp] theorem total_nil : total [] = 0 := by simp [total]

@[simp] theorem total_cons (x : Num) (r : List Num) : total (x :: r) = x.val + total r := by
  simp [total]

theorem total_nonneg (xs : List Num) (hn : ∀ x ∈ xs, 0 ≤ x.val) : 0 ≤ total xs := by
  induction xs with
  | nil => simp
  | cons x r ih =>
    have hx := hn x (by simp)
    have hr := ih (fun y hy => hn y (by simp [hy]))
    simp only [total_cons]
    omega

/-! ## Strings

A string is its UTF-16 code units, which is what `length`, `[i]` and `slice` see
in JavaScript. Lean's `String` can't hold a lone surrogate, so it isn't used. -/

abbrev Str := List Nat

/-- The UTF-16 code units of a character. -/
def units (c : Nat) : List Nat :=
  if c < 65536 then [c]
  else [55296 + (c - 65536) / 1024, 56320 + (c - 65536) % 1024]

/-- `js!"text"` is a string literal, written out as code units when it elaborates. -/
syntax "js!" str : term

macro_rules
  | `(js! $s:str) => do
    let codes := (s.getString.toList.map (fun c => units c.toNat)).flatten
    let items : Array (Lean.TSyntax `term) := codes.toArray.map (fun n => ⟨Lean.Syntax.mkNatLit n⟩)
    `(([$items,*] : Js.Str))

/-- `s[i]` -/
def charAt? (s : Str) (i : Num) : Option Str := (at_ s i).map (fun c => [c])

/-- `s.charAt(i)`: the empty string past the end. -/
def charAt (s : Str) (i : Num) : Str := (charAt? s i).getD []

/-- Does `pre` start `s`? -/
def startsWith (s pre : Str) : Bool := pre.isPrefixOf s

def endsWith (s suf : Str) : Bool := suf.reverse.isPrefixOf s.reverse

/-- The first position of `sub` in `s`, as a natural number. -/
def find? (s sub : Str) : Option Nat :=
  match s with
  | [] => if sub.isEmpty then some 0 else none
  | c :: rest =>
    if sub.isPrefixOf (c :: rest) then some 0 else (find? rest sub).map (· + 1)

def strIncludes (s sub : Str) : Bool := (find? s sub).isSome

/-- `s.indexOf(sub)` -/
def strIndexOf (s sub : Str) : Result Num :=
  match find? s sub with
  | some i => mk i
  | none => mk (-1)

/-- The last position of `sub` in `s`: a match in the tail is further along than one here. -/
def rfind? (s sub : Str) : Option Nat :=
  match s with
  | [] => if sub.isEmpty then some 0 else none
  | c :: rest =>
    match rfind? rest sub with
    | some i => some (i + 1)
    | none => if sub.isPrefixOf (c :: rest) then some 0 else none

/-- `s.lastIndexOf(sub)` -/
def strLastIndexOf (s sub : Str) : Result Num :=
  match rfind? s sub with
  | some i => mk i
  | none => mk (-1)

/-- `s.charCodeAt(i)`. Past the end JavaScript gives `NaN`, which isn't a `Num`, so the
    model stops there. -/
def charCodeAt (s : Str) (i : Num) : Result Num :=
  match at_ s i with
  | some c => mk c
  | none => fail .undef

/-- `s.substring(a, b)`: bounds are clamped and swapped if out of order. -/
def substring (s : Str) (a b : Num) : Str :=
  let clamp (i : Num) : Nat := Min.min i.val.toNat s.length
  let x := clamp a
  let y := clamp b
  (s.take (Max.max x y)).drop (Min.min x y)

/-- Characters `trim` removes. -/
def isSpace (c : Nat) : Bool :=
  (9 ≤ c ∧ c ≤ 13) ∨ c = 32 ∨ c = 160 ∨ c = 5760 ∨ (8192 ≤ c ∧ c ≤ 8202) ∨ c = 8232 ∨ c = 8233
    ∨ c = 8239 ∨ c = 8287 ∨ c = 12288 ∨ c = 65279

def trimStart (s : Str) : Str := s.dropWhile isSpace
def trimEnd (s : Str) : Str := (s.reverse.dropWhile isSpace).reverse
def trim (s : Str) : Str := trimEnd (trimStart s)

/-- `trim` never makes a string longer. -/
theorem trim_length_le (s : Str) : (trim s).length ≤ s.length := by
  have e1 : (trimStart s).length ≤ s.length :=
    (List.dropWhile_suffix (l := s) isSpace).sublist.length_le
  have e2 : (trimEnd (trimStart s)).length ≤ (trimStart s).length := by
    simp only [trimEnd, List.length_reverse]
    exact le_trans (List.dropWhile_suffix (l := (trimStart s).reverse) isSpace).sublist.length_le
      (le_of_eq (by simp only [List.length_reverse]))
  exact le_trans e2 e1

/-- `toLowerCase` for ASCII. Other text needs Unicode tables, so the model stops. -/
def toLower (s : Str) : Result Str :=
  if s.all (· < 128) then ok (s.map fun c => if 65 ≤ c ∧ c ≤ 90 then c + 32 else c) else fail .undef

/-- `toUpperCase` for ASCII. -/
def toUpper (s : Str) : Result Str :=
  if s.all (· < 128) then ok (s.map fun c => if 97 ≤ c ∧ c ≤ 122 then c - 32 else c) else fail .undef

/-- Splits at each `sep`, which must not be empty. `fuel` bounds the steps. -/
def splitGo (sep : Str) : Nat → Str → Str → List Str
  | 0, current, rest => [current ++ rest]
  | _ + 1, current, [] => [current]
  | fuel + 1, current, c :: rest =>
    if sep.isPrefixOf (c :: rest) then current :: splitGo sep fuel [] ((c :: rest).drop sep.length)
    else splitGo sep fuel (current ++ [c]) rest

/-- `s.split(sep)`. An empty separator gives each code unit. -/
def split (s sep : Str) : List Str :=
  if sep.isEmpty then s.map (fun c => [c]) else splitGo sep s.length [] s

/-- `xs.join(sep)` -/
def join (xs : List Str) (sep : Str) : Str := (xs.intersperse sep).flatten

/-- `s.replace(a, b)` and `s.replaceAll(a, b)`. `$` in `b` is a replacement
    pattern and an empty `a` has its own rules, so the model stops for those. -/
def replace (s a b : Str) : Result Str :=
  if b.contains 36 ∨ a.isEmpty then fail .undef else
  match find? s a with
  | some i => ok (s.take i ++ b ++ s.drop (i + a.length))
  | none => ok s

def replaceAll (s a b : Str) : Result Str :=
  if b.contains 36 ∨ a.isEmpty then fail .undef else ok (join (split s a) b)

/-! ### Step lemmas and equations for the string primitives -/

theorem find?_le_length {s sub : Str} {i : Nat} (h : find? s sub = some i) : i ≤ s.length := by
  induction s generalizing i with
  | nil => simp only [find?] at h; split at h <;> simp_all
  | cons c rest ih =>
    simp only [find?] at h
    split at h
    · simp_all
    · rename_i hne
      obtain ⟨j, hj, rfl⟩ : ∃ j, find? rest sub = some j ∧ j + 1 = i := by
        cases hr : find? rest sub with
        | none => simp [hr] at h
        | some j => simp [hr] at h; exact ⟨j, rfl, h⟩
      have := ih hj
      simp only [List.length_cons]; omega

/-- `s.indexOf(sub)`: the `some` position or `-1`. -/
@[step] theorem strIndexOf_spec (s sub : Str) (hl : s.length ≤ 9007199254740991) :
    strIndexOf s sub ⦃ r => r.val = match find? s sub with | some i => (i : Int) | none => -1 ⦄ := by
  simp only [strIndexOf]
  cases h : find? s sub with
  | some i =>
    have hi := find?_le_length h
    exact mk_spec _ (by omega) (by omega)
  | none => exact mk_spec _ (by omega) (by omega)

/-- `s.charCodeAt(i)` at an in-range index. -/
@[step] theorem charCodeAt_spec (s : Str) (i : Num) (c : Nat)
    (h0 : 0 ≤ i.val) (hi : s[i.val.toNat]? = some c) (hc : (c : Int) ≤ 9007199254740991) :
    charCodeAt s i ⦃ r => r.val = (c : Int) ⦄ := by
  rw [charCodeAt, at_, ite_eq_right (show ¬ i.val < 0 by omega), hi]
  exact mk_spec _ (by have := Nat.cast_nonneg (α := Int) c; omega) hc

/-- `s.toLowerCase()` on ASCII text. -/
@[step] theorem toLower_spec (s : Str) (h : s.all (· < 128) = true) :
    toLower s ⦃ r => r = s.map fun c => if 65 ≤ c ∧ c ≤ 90 then c + 32 else c ⦄ := by
  simp only [toLower, h, ite_eq_left trivial, WP.spec_ok]

/-- `s.toUpperCase()` on ASCII text. -/
@[step] theorem toUpper_spec (s : Str) (h : s.all (· < 128) = true) :
    toUpper s ⦃ r => r = s.map fun c => if 97 ≤ c ∧ c ≤ 122 then c - 32 else c ⦄ := by
  simp only [toUpper, h, ite_eq_left trivial, WP.spec_ok]

/-- `s.startsWith(pre)` is a prefix test. -/
@[simp] theorem startsWith_eq (s pre : Str) : startsWith s pre = pre.isPrefixOf s := rfl

/-- `split`'s work function makes at most `fuel + 1` pieces. -/
theorem splitGo_length_le (sep : Str) (fuel : Nat) (current rest : Str) :
    (splitGo sep fuel current rest).length ≤ fuel + 1 := by
  induction fuel generalizing current rest with
  | zero => simp [splitGo]
  | succ fuel ih =>
    match rest with
    | [] => simp [splitGo]
    | c :: rest' =>
      simp only [splitGo]
      split
      · exact Nat.succ_le_succ (ih [] _)
      · exact Nat.le_trans (ih _ _) (Nat.le_succ _)

/-- `s.split(sep)` makes at most `s.length + 1` pieces. -/
theorem split_length_le (s sep : Str) : (split s sep).length ≤ s.length + 1 := by
  simp only [split]
  split
  · rw [List.length_map]; exact Nat.le_succ _
  · exact splitGo_length_le _ _ _ _

/-! Regular expressions: a literal whose flags are at most `i` and `g`, built from code units,
classes, `.`, `^`, `$`, `*`, `+`, `?` and `|`. The translator refuses the rest. `+` is `a a*`. -/
inductive Re where
  | eps
  | chr (c : Nat)
  | cls (neg : Bool) (ranges : List (Nat × Nat))
  | dot
  | bol
  | eol
  | seq (a b : Re)
  | alt (a b : Re)
  | star (a : Re)
  | opt (a : Re)
  deriving DecidableEq, Repr, Inhabited

def Re.size : Re → Nat
  | .seq a b | .alt a b => a.size + b.size + 1
  | .star a | .opt a => a.size + 1
  | _ => 1

/-- Without `u`, `i` compares the upper case of each code unit. Only ASCII is modelled. -/
def reCanon (ic : Bool) (c : Nat) : Nat := if ic ∧ 97 ≤ c ∧ c ≤ 122 then c - 32 else c

def reInCls (ic : Bool) (rs : List (Nat × Nat)) (c : Nat) : Bool :=
  let hit := fun u => rs.any fun (a, b) => decide (a ≤ u ∧ u ≤ b)
  hit c || (ic && (hit (reCanon true c) || (decide (65 ≤ c ∧ c ≤ 90) && hit (c + 32))))

/-- Matches `r` at `i`, then runs `k` on where it ended. It backtracks in JavaScript's order: the
    left of `|` first, as many repeats as possible first, and a repeat that matches nothing fails.
    `none` is out of fuel. -/
def reStep (ic : Bool) (s : Str) : Nat → Re → Nat → (Nat → Option (Option Nat)) → Option (Option Nat)
  | 0, _, _, _ => none
  | f + 1, r, i, k => match r with
    | .eps => k i
    | .chr c => match s[i]? with
      | some u => if reCanon ic u = reCanon ic c then k (i + 1) else some none
      | none => some none
    | .cls neg rs => match s[i]? with
      | some u => if reInCls ic rs u != neg then k (i + 1) else some none
      | none => some none
    | .dot => match s[i]? with
      | some u => if u = 10 ∨ u = 13 ∨ u = 8232 ∨ u = 8233 then some none else k (i + 1)
      | none => some none
    | .bol => if i = 0 then k i else some none
    | .eol => if i = s.length then k i else some none
    | .seq a b => reStep ic s f a i fun j => reStep ic s f b j k
    | .alt a b => match reStep ic s f a i k with
      | some none => reStep ic s f b i k
      | m => m
    | .star a => match reStep ic s f a i (fun j => if j = i then some none else reStep ic s f (.star a) j k) with
      | some none => k i
      | m => m
    | .opt a => match reStep ic s f a i (fun j => if j = i then some none else k j) with
      | some none => k i
      | m => m

/-- Where a match of `r` starting at `i` ends. -/
def reMatchAt (r : Re) (ic : Bool) (s : Str) (i : Nat) : Option (Option Nat) :=
  reStep ic s ((s.length + 2) * (r.size + 2) * 4) r i fun j => some (some j)

/-- The first match at or after `i`, of the `n` places tried: where it starts and ends. -/
def reSearch (r : Re) (ic : Bool) (s : Str) : Nat → Nat → Option (Option (Nat × Nat))
  | 0, _ => some none
  | n + 1, i => match reMatchAt r ic s i with
    | none => none
    | some (some j) => some (some (i, j))
    | some none => reSearch r ic s n (i + 1)

/-- Each match from `i` on, as `replace` with `g` finds them: after an empty match the search
    moves on one code unit. -/
def reAll (r : Re) (ic : Bool) (s : Str) : Nat → Nat → Option (List (Nat × Nat))
  | 0, _ => none
  | n + 1, i => if s.length < i then some [] else
    match reSearch r ic s (s.length + 1 - i) i with
    | none => none
    | some none => some []
    | some (some (a, b)) => (fun ms => (a, b) :: ms) <$> reAll r ic s n (if b = a then b + 1 else b)

/-- With `i` the model stops on text that isn't ASCII. -/
def reOk (ic : Bool) (s : Str) : Bool := !ic || s.all (· < 128)

/-- `re.test(s)` and `s.match(re) !== null`. -/
def reTest (r : Re) (ic : Bool) (s : Str) : Result Bool :=
  if !reOk ic s then fail .undef else
  match reSearch r ic s (s.length + 1) 0 with
  | some m => ok m.isSome
  | none => fail .undef

/-- `re.test(s)` reduces to the outcome of `reSearch`. To reason about a concrete
    `re.test`, supply the match that `reSearch r ic s (s.length + 1) 0` computes
    (typically `by decide` for a literal pattern and literal text). -/
@[step] theorem reTest_spec (r : Re) (ic : Bool) (s : Str) (m : Option (Nat × Nat))
    (h0 : reOk ic s = true) (hm : reSearch r ic s (s.length + 1) 0 = some m) :
    reTest r ic s ⦃ r' => r' = m.isSome ⦄ := by
  simp [reTest, h0, hm, WP.spec_ok]

def reSplice (s b : Str) : Nat → List (Nat × Nat) → Str
  | p, [] => s.drop p
  | p, (i, j) :: ms => (s.take i).drop p ++ b ++ reSplice s b j ms

/-- `s.replace(re, b)`, every match with `g` (also `replaceAll`). `$` in `b` stops the model. -/
def reReplace (r : Re) (ic all : Bool) (s b : Str) : Result Str :=
  if b.contains 36 ∨ !reOk ic s then fail .undef else
  match (if all then reAll r ic s (s.length + 2) 0 else Option.toList <$> reSearch r ic s (s.length + 1) 0) with
  | some ms => ok (reSplice s b 0 ms)
  | none => fail .undef

/-- `s.split(re)` as `RegExp.prototype[Symbol.split]` does it: a match is tried at each `q`, and
    one that ends where the piece began moves `q` on instead. -/
def reSplitGo (r : Re) (ic : Bool) (s : Str) : Nat → Nat → Nat → Option (List Str)
  | 0, _, _ => none
  | n + 1, p, q => if s.length ≤ q then some [s.drop p] else
    match reMatchAt r ic s q with
    | none => none
    | some none => reSplitGo r ic s n p (q + 1)
    | some (some e) => if e = p then reSplitGo r ic s n p (q + 1)
      else (fun xs => (s.take q).drop p :: xs) <$> reSplitGo r ic s n e e

/-- `s.split(re)`, for a pattern without capturing groups. -/
def reSplit (r : Re) (ic : Bool) (s : Str) : Result (List Str) :=
  if !reOk ic s then fail .undef else
  if s.isEmpty then match reMatchAt r ic s 0 with
    | some (some _) => ok []
    | some none => ok [[]]
    | none => fail .undef
  else match reSplitGo r ic s (2 * s.length + 2) 0 0 with
    | some xs => ok xs
    | none => fail .undef

/-- `a < b` compares code units in order. -/
def strLt : Str → Str → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x < y ∨ (x = y ∧ strLt xs ys)

/-- A whole number as text. Every safe integer prints without an exponent. -/
def intStr (v : Int) : Str := (toString v).toList.map Char.toNat

def numStr (x : Num) : Str := intStr x.val
def boolStr (b : Bool) : Str := if b then js!"true" else js!"false"

/-- `Number.isFinite(x)` and friends. A `Num` is always a safe integer, so this is true.
    It stays a name so that a test on it isn't simplified away. -/
def isFinite (_ : Num) : Bool := true

/-- `Number.isNaN(x)`, false for the same reason. -/
def isNaN (_ : Num) : Bool := false

/-- `Number.isInteger`: every `Num` is a whole number. -/
def isInteger (_ : Num) : Bool := true

/-- `Number.isSafeInteger`: every `Num` is in the exact range. -/
def isSafeInteger (_ : Num) : Bool := true

/-- `x.toFixed(d)`. A safe integer has no fraction to round, so this only pads. `d` must be
    in the range JavaScript allows, and it throws otherwise. -/
def toFixed (x d : Num) : Result Str :=
  if d.val = 0 then ok (numStr x)
  else if 0 < d.val ∧ d.val ≤ 100 then ok (numStr x ++ [46] ++ List.replicate d.val.toNat 48)
  else fail .undef

/-- `parseInt(s, 10)`, or `parseInt(s)` when `auto` is set. Without a radix, a `0x` prefix
    means hexadecimal, and the model stops there. No digits gives `NaN`, where it stops too. -/
def parseIntStr (auto : Bool) (s : Str) : Result Num :=
  let t := trimStart s
  let (neg, u) := match t with
    | 45 :: r => (true, r)
    | 43 :: r => (false, r)
    | r => (false, r)
  let hex := match u with
    | 48 :: x :: _ => x == 120 || x == 88
    | _ => false
  let digits := u.takeWhile (fun c => 48 ≤ c && c ≤ 57)
  if (auto && hex) || digits.isEmpty then fail .undef
  else
    let n : Int := digits.foldl (fun a c => a * 10 + ((c : Int) - 48)) 0
    -- A minus sign on zero gives `-0`, which isn't a `Num`.
    if neg && n == 0 then fail .undef else mk (if neg then -n else n)

/-- `Number(s)` for whitespace around an optional sign and decimal digits, and for blank
    text, which is `0`. Fractions, exponents, other bases, `Infinity`, `-0` and `NaN` stop the model. -/
def numOfStr (s : Str) : Result Num :=
  let t := trim s
  let (neg, u) := match t with
    | 45 :: r => (true, r)
    | 43 :: r => (false, r)
    | r => (false, r)
  if t.isEmpty then mk 0
  else if u.isEmpty || !u.all (fun c => 48 ≤ c && c ≤ 57) then fail .undef
  else
    let n : Int := u.foldl (fun a c => a * 10 + ((c : Int) - 48)) 0
    if neg && n == 0 then fail .undef else mk (if neg then -n else n)

/-- `Number(b)` -/
def boolNum (b : Bool) : Num := if b then ⟨1, by decide, by decide⟩ else ⟨0, by decide, by decide⟩

/-- `Array.isArray(xs)`. It stays a name so that a test on it isn't simplified away. -/
def isArray {α} (_ : List α) : Bool := true

/-- The first `k` units of `fill` repeated. -/
def padding (fill : Str) (k : Nat) : Str := (List.range k).map fun i => fill.getD (i % fill.length) 0

/-- `s.padStart(n, fill)`. Past `2 ^ 20` units the model stops, far below the longest string
    JavaScript allows. -/
def padStart (s : Str) (n : Num) (fill : Str) : Result Str :=
  if n.val ≤ s.length ∨ fill = [] then ok s
  else if n.val ≤ 2 ^ 20 then ok (padding fill (n.val.toNat - s.length) ++ s)
  else fail .undef

/-- `s.padEnd(n, fill)`, on the same terms. -/
def padEnd (s : Str) (n : Num) (fill : Str) : Result Str :=
  if n.val ≤ s.length ∨ fill = [] then ok s
  else if n.val ≤ 2 ^ 20 then ok (s ++ padding fill (n.val.toNat - s.length))
  else fail .undef

/-- Where `xs.at(i)` reads: a negative index counts from the end. -/
def relIndex (len : Nat) (i : Int) : Int := if i < 0 then len + i else i

/-- `xs.at(i)` -/
def atRel {α} (xs : List α) (i : Num) : Option α :=
  if relIndex xs.length i.val < 0 then none else xs[(relIndex xs.length i.val).toNat]?

/-- `s.at(i)` -/
def strAt (s : Str) (i : Num) : Option Str := (atRel s i).map fun c => [c]

/-- `xs.lastIndexOf(v)`, for values compared by value. -/
def lastIndexOf {α} [DecidableEq α] (xs : List α) (v : α) : Result Num :=
  match xs.reverse.idxOf? v with
  | some i => mk ((xs.length : Int) - 1 - i)
  | none => mk (-1)

/-- `s.repeat(n)`. A negative count throws, and past `2 ^ 20` units the model stops. -/
def strRepeat (s : Str) (n : Num) : Result Str :=
  if n.val < 0 then fail .undef
  else if s = [] then ok []
  else if s.length * n.val.toNat ≤ 2 ^ 20 then ok (List.replicate n.val.toNat s).flatten
  else fail .undef

/-- `xs.flat()` on an array of arrays. -/
def flat {α} (xss : List (List α)) : List α := xss.flatten

/-- `xs.findIndex(f)`, counting from `i`. -/
def findIndexFrom {α} (f : α → Result Bool) : List α → Nat → Result Num
  | [], _ => mk (-1)
  | x :: rest, i => do
    let hit ← f x
    if hit then mk i else findIndexFrom f rest (i + 1)

def findIndex {α} (f : α → Result Bool) (xs : List α) : Result Num := findIndexFrom f xs 0

def undefinedStr : Str := js!"undefined"
def nullStr : Str := js!"null"

/-- `${x}` where `x` may be `undefined`. -/
def showUndef {α} (f : α → Str) : Option α → Str
  | some a => f a
  | none => undefinedStr

/-- `${x}` where `x` may be `null`. -/
def showNull {α} (f : α → Str) : Option α → Str
  | some a => f a
  | none => nullStr

/-! ## Maps and sets

Both keep insertion order, like JavaScript's. Keys are compared by value, which
is correct for the keys the translator allows: numbers, strings and booleans. -/

abbrev Dict (K V : Type) := List (K × V)

def dictGet {K V} [DecidableEq K] (m : Dict K V) (k : K) : Option V := m.lookup k

def dictHas {K V} [DecidableEq K] (m : Dict K V) (k : K) : Bool := (m.lookup k).isSome

/-- `m.set(k, v)`. An existing key keeps its position. -/
def dictSet {K V} [DecidableEq K] (m : Dict K V) (k : K) (v : V) : Dict K V :=
  if dictHas m k then m.map (fun e => if e.1 = k then (k, v) else e) else m ++ [(k, v)]

def dictDelete {K V} [DecidableEq K] (m : Dict K V) (k : K) : Dict K V := m.filter (fun e => e.1 ≠ k)

/-- Names `Object.prototype` answers for, so `r[k]` and `k in r` would see them, and the class tag. -/
def protoNames : List Str := [js!"__proto__", js!"__class", js!"constructor", js!"hasOwnProperty", js!"isPrototypeOf",
  js!"propertyIsEnumerable", js!"toLocaleString", js!"toString", js!"valueOf", js!"__defineGetter__",
  js!"__defineSetter__", js!"__lookupGetter__", js!"__lookupSetter__"]

/-- Keys a record of dynamic keys can hold: plain ASCII, not an array index (JavaScript lists those
    first) and not in `protoNames`. Any other key stops the model. -/
def keyOk (s : Str) : Bool := !s.isEmpty && s.all (· < 128) && !s.all (fun c => 48 ≤ c && c ≤ 57) && !protoNames.contains s

/-- `r[k]` on a record of dynamic keys. -/
def recGet {α} (d : Dict Str α) (k : Str) : Result (Option α) := if keyOk k then ok (dictGet d k) else fail .undef

/-- `k in r` -/
def recHas {α} (d : Dict Str α) (k : Str) : Result Bool := if keyOk k then ok (dictHas d k) else fail .undef

/-- `r[k] = v` -/
def recSet {α} (d : Dict Str α) (k : Str) (v : α) : Result (Dict Str α) := if keyOk k then ok (dictSet d k v) else fail .undef

/-- `s.add(v)` -/
def setAdd {K} [DecidableEq K] (s : List K) (v : K) : List K := if s.contains v then s else s ++ [v]

def setDelete {K} [DecidableEq K] (s : List K) (v : K) : List K := s.filter (· ≠ v)

/-- `new Set(xs)`: the first occurrence of each value, in order. -/
def setOf {K} [DecidableEq K] (xs : List K) : List K := xs.foldl setAdd []

/-- `s.has(v)` -/
def setHas {K} [DecidableEq K] (s : List K) (v : K) : Bool := s.contains v

/-- A number for the differential test. Inputs are always safe integers. -/
def lit (v : Int) : Num :=
  if h : -9007199254740991 ≤ v ∧ v ≤ 9007199254740991 then ⟨v, h.1, h.2⟩ else default

/-- The translator emits numerals as `Js.lit v`, so goals carry `lit` rather than
    `Num.mk`'s proof arguments. `.val` unfolds it; for a concrete literal `simp`
    discharges the bound check and leaves the integer. -/
@[simp, scalar_tac_simps] theorem lit_val (v : Int) :
    (lit v).val = if -9007199254740991 ≤ v ∧ v ≤ 9007199254740991 then v else 0 := by
  simp only [lit]
  split <;> rfl

/-- Compares the model with what Node computed. `expected` is `none` when Node
    produced something other than a value of the declared type. The model may
    always fail, but when it returns a value, Node must have returned the same. -/
def agree {α} [DecidableEq α] (label : String) (r : Result α) (expected : Option α) (threw : Bool) : IO Unit :=
  match r.match with
  | .ok v => IO.println (if some v = expected then s!"PROOFCI_DIFF agree {label}" else s!"PROOFCI_DIFF differ {label}")
  | .vis (.fail .panic) _ => IO.println (if threw then s!"PROOFCI_DIFF agree {label}" else s!"PROOFCI_DIFF differ {label}")
  | _ => IO.println s!"PROOFCI_DIFF failed {label}"

/-- A JavaScript `number` in full: IEEE-754 binary64 (`Core.F64`). -/
structure Dbl where
  f : Core.F64
  deriving DecidableEq, Repr

instance : Inhabited Dbl := ⟨⟨.fin false 0⟩⟩

namespace Dbl

def add (x y : Dbl) : Result Dbl := ok ⟨x.f.add y.f⟩
def sub (x y : Dbl) : Result Dbl := ok ⟨x.f.sub y.f⟩
def mul (x y : Dbl) : Result Dbl := ok ⟨x.f.mul y.f⟩
def div (x y : Dbl) : Result Dbl := ok ⟨x.f.div y.f⟩
/-- `x % y`: the sign of the dividend, exactly as JavaScript. -/
def rem (x y : Dbl) : Result Dbl := ok ⟨x.f.rem y.f⟩
def neg (x : Dbl) : Result Dbl := ok ⟨x.f.neg⟩

/-- `Math.floor`, `ceil`, `trunc`, `round`, `sign` and `abs`, named by their `F64` op. -/
def math (f : Core.F64 → Core.F64) (x : Dbl) : Result Dbl := ok ⟨f x.f⟩

/-- `Math.min(x, y)` -/
def min (x y : Dbl) : Dbl := ⟨x.f.fmin y.f⟩
/-- `Math.max(x, y)` -/
def max (x y : Dbl) : Dbl := ⟨x.f.fmax y.f⟩

/-- `Number.isFinite` -/
def isFinite (x : Dbl) : Bool := x.f.isFin
/-- `Number.isNaN` -/
def isNaN (x : Dbl) : Bool := x.f.isNan
/-- `Number.isInteger` -/
def isInteger (x : Dbl) : Bool := x.f.isInt'
/-- `Number.isSafeInteger` -/
def isSafe (x : Dbl) : Bool := x.f.isSafe

/-- `if (x)` on a possibly missing double: `0`, `-0` and `NaN` are falsy. -/
def truthy : Option Dbl → Bool
  | some ⟨.fin _ 0⟩ | some ⟨.nan⟩ | none => false
  | some _ => true

/-- A double read back as a `Num`, when it already holds an integer in the safe
range (`-0` reads as `0`). Anything else fails, like `Core.asNum`. -/
def numOf (x : Dbl) : Result Num :=
  match x.f with
  | .fin s n => if n % Core.F64.unit = 0 then Js.mk (Core.F64.signed s (n / Core.F64.unit)) else fail .undef
  | _ => fail .undef

/-- A safe integer read as a double; safe integers are exactly representable.
Used for constants whose double re-evaluation is refused: exact, but the
bridge does not prove the lifted result. -/
def ofNum (x : Num) : Dbl := ⟨Core.F64.ofInt x.val⟩

/-- Lifts a computed integer into a double. Only for values whose expression
can't produce `-0` (see `ofNumNe` for the case that can). -/
def ofNumR (x : Result Num) : Result Dbl := do
  let v ← x
  ok (ofNum v)

/-- The lift double code uses when re-evaluating a constant is refused. `0`
fails: JavaScript may have computed `-0` there, which `Num` cannot
distinguish, so the lift fails closed rather than erase a sign. -/
def ofNumNe (x : Result Num) : Result Dbl := do
  let v ← x
  if v.val = 0 then fail .undef else ok (ofNum v)

/-- The length as a double, for code working on doubles. -/
def len {α} (xs : List α) : Result Dbl := ok ⟨Core.F64.ofInt xs.length⟩

/-- `s.indexOf(sub)` as a double. -/
def strIndexOf (s sub : Str) : Result Dbl := do
  let r ← Js.strIndexOf s sub
  ok ⟨Core.F64.ofInt r.val⟩

/-- `s.lastIndexOf(sub)` as a double. -/
def strLastIndexOf (s sub : Str) : Result Dbl := do
  let r ← Js.strLastIndexOf s sub
  ok ⟨Core.F64.ofInt r.val⟩

/-- `s.charCodeAt(i)` as a double. -/
def charCodeAt (s : Str) (i : Num) : Result Dbl := do
  let r ← Js.charCodeAt s i
  ok ⟨Core.F64.ofInt r.val⟩

/-- `xs.indexOf(v)` as a double. -/
def indexOf {α} [DecidableEq α] (xs : List α) (v : α) : Result Dbl := do
  let r ← Js.indexOf xs v
  ok ⟨Core.F64.ofInt r.val⟩

/-- `xs.lastIndexOf(v)` as a double. -/
def lastIndexOf {α} [DecidableEq α] (xs : List α) (v : α) : Result Dbl := do
  let r ← Js.lastIndexOf xs v
  ok ⟨Core.F64.ofInt r.val⟩

/-- `xs.findIndex(...)` as a double. -/
def findIndex {α} (f : α → Result Bool) (xs : List α) : Result Dbl := do
  let r ← Js.findIndex f xs
  ok ⟨Core.F64.ofInt r.val⟩

/-- The real number a finite double stands for, as a rational; `0` for `NaN` and
the infinities, which have none. Contracts use it to talk about value, not bits. -/
def toRat (x : Dbl) : Rat :=
  match x.f with
  | .fin s n => (if s then -(n : Rat) else n) / 2 ^ 1074
  | _ => 0


/-- `Js.Dbl.toRat` is the model's `toRatD`, so `Core.F64` order lemmas apply. -/
theorem toRat_eq (x : Dbl) : toRat x = x.f.toRatD := by
  cases x with
  | mk f =>
    cases f with
    | fin s n =>
      rw [Core.F64.toRat_fin, Int.cast_natCast, Core.F64.unit_rat]
      cases s <;> simp [toRat, Core.F64.signed, Int.cast_natCast]
    | nan => rfl
    | inf s => rfl

/-- `ofDecimal m e`: the nearest double to `m * 10^-e`, so `ofDecimal 1299 2` is
`12.99`. Contracts use it to write readable decimal literals; `Core.F64.ofDecimal`
rounds to the nearest binary64, ties to even — the IEEE-correct value as long as
`m` and `10^e` are safe integers (any sane fixed-point literal). -/
def ofDecimal (m : Int) (e : Nat) : Dbl :=
  ⟨Core.F64.ofDecimal m e⟩

/-- A literal, by its binary64 bits: what a test vector or a generated term carries. -/
def lit (b : Nat) : Dbl := ⟨Core.F64.ofBits b⟩

/-- `"12"` or `"12.99"` (optional leading `-`) → `(magnitude, scale)` for `ofDecimal`. -/
private def parseDecimal (s : String) : Option (Int × Nat) := do
  let neg := s.startsWith "-"
  let s := if neg then String.ofList (s.toList.drop 1) else s
  match String.splitOn s "." with
  | [w] =>
    let w ← String.toNat? w
    pure ((if neg then -(w : Int) else (w : Int)), 0)
  | [w, f] =>
    let w ← String.toNat? w
    let fnum ← String.toNat? f
    let e := String.length f
    let mag : Int := (w : Int) * 10 ^ e + fnum
    pure ((if neg then -mag else mag), e)
  | _ => none

/-- `dbl!"12.99"`: a decimal literal compiled to `Js.Dbl.lit <bits>` — the nearest
binary64 is computed at elaboration time, so in contracts it reads as a decimal
while comparing to `lit`/bits stays `decide`-cheap. -/
elab "dbl!" s:str : term => do
  match parseDecimal s.getString with
  | some (m, e) =>
    -- `ofDecimal 0 e` is `+0`; a signed zero literal keeps `-0`'s bits.
    let bits := if m == 0 && s.getString.startsWith "-" then 0x8000000000000000
      else Core.F64.toBits (Core.F64.ofDecimal m e)
    pure (Lean.mkApp (Lean.mkConst ``Js.Dbl.lit) (Lean.Expr.lit (.natVal bits)))
  | none => throwError "dbl!: expected a decimal like \"12\" or \"12.99\", got {s.getString.quote}"


end Dbl

end Js
