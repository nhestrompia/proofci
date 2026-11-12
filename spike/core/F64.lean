/-! # binary64 (spike)

Every finite double is a whole multiple of 2⁻¹⁰⁷⁴, so a finite value is that multiple
and a sign. There are no exponents to align, each value has one form, and `-0` is
`fin true 0`. Results are computed exactly and then rounded to nearest, ties to even. -/

namespace Core

inductive F64 where
  | nan
  | inf (neg : Bool)
  | fin (neg : Bool) (n : Nat)
  deriving DecidableEq, Repr

namespace F64

/-- 2¹⁰²⁴ in units of 2⁻¹⁰⁷⁴: the first magnitude that overflows. -/
def limit : Nat := 2 ^ 2098

/-- Rounds `n · 2^(-1074 - extra)`, where `sticky` says something nonzero lies below `n`. -/
def round (neg : Bool) (n extra : Nat) (sticky : Bool) : F64 :=
  if n = 0 then fin neg 0 else
  let s := max (Nat.log2 n + 1 - 53) extra
  if s = 0 then (if limit ≤ n then inf neg else fin neg n) else
  let kept := n / 2 ^ s
  let rest := n % 2 ^ s
  let half := 2 ^ (s - 1)
  let up := decide (half < rest) || (decide (rest = half) && (sticky || decide (kept % 2 = 1)))
  let m := if up then kept + 1 else kept
  let r := m * 2 ^ (s - extra)
  if limit ≤ r then inf neg else fin neg r

def signed (neg : Bool) (n : Nat) : Int := if neg then -(n : Int) else n

def neg : F64 → F64
  | nan => nan
  | inf s => inf (!s)
  | fin s n => fin (!s) n

def add : F64 → F64 → F64
  | nan, _ | _, nan => nan
  | inf a, inf b => if a = b then inf a else nan
  | inf a, fin _ _ | fin _ _, inf a => inf a
  | fin a x, fin b y =>
    let r := signed a x + signed b y
    if r = 0 then fin (a && b) 0 else round (decide (r < 0)) r.natAbs 0 false

def sub (x y : F64) : F64 := add x (neg y)

def mul : F64 → F64 → F64
  | nan, _ | _, nan => nan
  | inf a, inf b => inf (a != b)
  | inf a, fin b y | fin b y, inf a => if y = 0 then nan else inf (a != b)
  | fin a x, fin b y => round (a != b) (x * y) 1074 false

def div : F64 → F64 → F64
  | nan, _ | _, nan => nan
  | inf _, inf _ => nan
  | inf a, fin b _ => inf (a != b)
  | fin a _, inf b => fin (a != b) 0
  | fin a x, fin b y =>
    if y = 0 then (if x = 0 then nan else inf (a != b))
    else if x = 0 then fin (a != b) 0
    else
      let k := Nat.log2 y + 64
      let top := x * 2 ^ (1074 + k)
      round (a != b) (top / y) k (decide (top % y ≠ 0))

/-- `%`: the sign of the dividend. The remainder of two doubles is always exact. -/
def rem : F64 → F64 → F64
  | nan, _ | _, nan | inf _, _ => nan
  | fin a x, inf _ => fin a x
  | fin a x, fin _ y => if y = 0 then nan else fin a (x % y)

def unit : Nat := 2 ^ 1074

def trunc : F64 → F64
  | fin s n => fin s (n / unit * unit)
  | x => x

def floor : F64 → F64
  | fin true n => if n % unit = 0 then fin true n else fin true ((n / unit + 1) * unit)
  | x => trunc x

def ceil : F64 → F64
  | fin false n => if n % unit = 0 then fin false n else fin false ((n / unit + 1) * unit)
  | fin true n => if n / unit = 0 then fin true 0 else fin true (n / unit * unit)
  | x => x

def lt : F64 → F64 → Bool
  | nan, _ | _, nan => false
  | inf a, inf b => a && !b
  | inf a, fin _ _ => a
  | fin _ _, inf b => !b
  | fin a x, fin b y => decide (signed a x < signed b y)

def le (x y : F64) : Bool := lt x y || eq' x y
where eq' : F64 → F64 → Bool
  | nan, _ | _, nan => false
  | inf a, inf b => a == b
  | fin a x, fin b y => decide (signed a x = signed b y)
  | _, _ => false

/-- `===`: `NaN` differs from itself, and `-0` equals `0`. -/
def eq (x y : F64) : Bool := le.eq' x y

def ofInt (a : Int) : F64 := fin (decide (a < 0)) (a.natAbs * unit)

/-- The array slot a number names, if it names one. `-0` is slot 0. -/
def index : F64 → Option Nat
  | fin neg n => if n = 0 then some 0 else if !neg && n % unit = 0 then some (n / unit) else none
  | _ => none

def ofBits (b : Nat) : F64 :=
  let neg := decide (2 ^ 63 ≤ b)
  let e := (b / 2 ^ 52) % 2048
  let m := b % 2 ^ 52
  if e = 2047 then (if m = 0 then inf neg else nan)
  else if e = 0 then fin neg m
  else fin neg ((2 ^ 52 + m) * 2 ^ (e - 1))

def toBits : F64 → Nat
  | nan => 0x7ff8000000000000
  | inf s => (if s then 2 ^ 63 else 0) + 0x7ff0000000000000
  | fin s n =>
    let sign := if s then 2 ^ 63 else 0
    if n < 2 ^ 52 then sign + n else
    let e := Nat.log2 n + 1 - 52
    sign + e * 2 ^ 52 + (n / 2 ^ (e - 1) - 2 ^ 52)

end F64
end Core
