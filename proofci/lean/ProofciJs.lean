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

@[simp] theorem map_nil {α β} (f : α → Result β) : map f [] = ok [] := rfl
@[simp] theorem filter_nil {α} (f : α → Result Bool) : filter f [] = ok [] := rfl
@[simp] theorem reduce_nil {α β} (f : β → α → Result β) (acc : β) : reduce f acc [] = ok acc := rfl

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

/-- Compares the model with what Node computed. `expected` is `none` when Node
    produced something other than a value of the declared type. The model may
    always fail, but when it returns a value, Node must have returned the same. -/
def agree {α} [DecidableEq α] (label : String) (r : Result α) (expected : Option α) (threw : Bool) : IO Unit :=
  match r.match with
  | .ok v => IO.println (if some v = expected then s!"PROOFCI_DIFF agree {label}" else s!"PROOFCI_DIFF differ {label}")
  | .vis (.fail .panic) _ => IO.println (if threw then s!"PROOFCI_DIFF agree {label}" else s!"PROOFCI_DIFF differ {label}")
  | _ => IO.println s!"PROOFCI_DIFF failed {label}"

end Js
