import Aeneas

set_option exponentiation.threshold 4096
set_option maxRecDepth 1000000
set_option maxHeartbeats 1600000

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

theorem signed_false (n : Nat) : signed false n = (n : Int) := rfl
theorem signed_true (n : Nat) : signed true n = -(n : Int) := rfl

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

theorem unit_pos : 0 < unit := Nat.two_pow_pos 1074

/-- `unit / 2` as a literal, for error bounds stated in `unit`s. -/
theorem unit_half : (unit : Int) / 2 = 2 ^ 1073 := by
  have e : (unit : Int) = 2 * 2 ^ 1073 := by
    exact_mod_cast (by unfold unit; rw [pow_succ'])
  rw [e]; omega

theorem unit_rat : ((unit : Rat)) = (2 : Rat) ^ 1074 := by
  unfold unit; rw [Nat.cast_pow]; norm_num

/-- Multiple of `unit` `floor` lands on: for negatives, the ceil of the magnitude. -/
def magUnit (s : Bool) (n : Nat) : Nat :=
  n / unit + (if s = true ∧ n % unit ≠ 0 then 1 else 0)

theorem magUnit_false (n : Nat) : magUnit false n = n / unit := by simp [magUnit]

theorem magUnit_true_of_mod {n : Nat} (h : n % unit = 0) : magUnit true n = n / unit := by
  simp only [magUnit, true_and, h, ne_self_iff_false, ite_false, add_zero]

theorem magUnit_true_of_mod_ne {n : Nat} (h : n % unit ≠ 0) :
    magUnit true n = n / unit + 1 := by
  simp only [magUnit, true_and]
  rw [ite_eq_left h]

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

/-- `Math.min(x, y)`: `NaN` wins, and `-0` is below `0`. -/
def fmin (x y : F64) : F64 := match x, y with
  | nan, _ | _, nan => nan
  | x, y => if x.lt y then x else if y.lt x then y else match x with
    | fin true 0 => x
    | _ => y

/-- `Math.max(x, y)`: `NaN` wins, and `0` is above `-0`. -/
def fmax (x y : F64) : F64 := match x, y with
  | nan, _ | _, nan => nan
  | x, y => if x.lt y then y else if y.lt x then x else match x with
    | fin false 0 => x
    | _ => y

/-- `Math.abs`: `NaN` stays `NaN`, `-0` becomes `0`. -/
def abs : F64 → F64
  | nan => nan
  | inf _ => inf false
  | fin _ n => fin false n

/-- `Math.sign`: `NaN` stays `NaN`, a zero keeps its sign, everything else is `±1`. -/
def sign : F64 → F64
  | nan => nan
  | inf neg => fin neg unit
  | fin neg n => if n = 0 then fin neg n else fin neg unit

/-- `Math.round`: the nearest integer, ties going toward `+∞`. `Math.round (-0.5)`
is `-0`, which the `fin neg 0` form keeps. -/
def jsround : F64 → F64
  | nan => nan
  | inf neg => inf neg
  | fin neg n =>
    let q := n / unit
    let r := n % unit
    if r * 2 < unit then fin neg (q * unit)
    else if r * 2 = unit then fin neg ((q + if neg then 0 else 1) * unit)
    else fin neg ((q + 1) * unit)

theorem floor_fin_false (n : Nat) :
    (fin false n).floor = fin false (n / unit * unit) := rfl

theorem floor_fin_true (n : Nat) :
    (fin true n).floor =
      (if n % unit = 0 then fin true n else fin true ((n / unit + 1) * unit)) := rfl

theorem ceil_fin_false (n : Nat) :
    (fin false n).ceil =
      (if n % unit = 0 then fin false n else fin false ((n / unit + 1) * unit)) := rfl

theorem ceil_fin_true (n : Nat) :
    (fin true n).ceil =
      (if n / unit = 0 then fin true 0 else fin true (n / unit * unit)) := rfl

theorem jsround_fin (neg : Bool) (n : Nat) :
    (fin neg n).jsround =
      (if n % unit * 2 < unit then fin neg (n / unit * unit)
       else if n % unit * 2 = unit then fin neg ((n / unit + (if neg then 0 else 1)) * unit)
       else fin neg ((n / unit + 1) * unit)) := rfl

/-- `Number.isFinite`: anything but `NaN` and the infinities. -/
def isFin : F64 → Bool
  | fin _ _ => true
  | _ => false

/-- `Number.isNaN`. -/
def isNan : F64 → Bool
  | nan => true
  | _ => false

/-- `Number.isInteger`: a finite whole number of `unit`s. -/
def isInt' : F64 → Bool
  | fin _ n => n % unit = 0
  | _ => false

/-- `Number.isSafeInteger`: an integer that fits in the exact range. -/
def isSafe : F64 → Bool
  | fin _ n => n % unit = 0 && n / unit ≤ 9007199254740991
  | _ => false

/-- `m · 10^(-e)` rounded to the nearest binary64, ties to even — so contracts can
write `ofDecimal 1299 2` for `12.99` instead of a bit pattern. -/
def ofDecimal (m : Int) (e : Nat) : F64 :=
  let n := m.natAbs * 2 ^ 2098
  let d := 10 ^ e
  round (decide (m < 0)) (n / d) 1024 (decide (n % d ≠ 0))

/-- The rational a finite value stands for; `none` for `NaN` and the infinities. -/
def toRat : F64 → Option Rat
  | fin s n => some ((if s then -(n : Rat) else n) / ((unit : Int) : Rat))
  | _ => none

/-- The same value as a function into `Rat`, `0` where there is none — contracts
that already know the result is finite read more easily with it. -/
def toRatD (x : F64) : Rat := (toRat x).getD 0

theorem toRat_eq_some {x : F64} (h : x.isFin = true) : ∃ r, x.toRat = some r := by
  cases x <;> simp [isFin] at h ⊢
  · rename_i s n; exact ⟨_, rfl⟩

/-- `toRatD` of a finite value is its signed integer magnitude scaled by `unit`. -/
theorem toRat_fin (s : Bool) (n : Nat) :
    (fin s n).toRatD = (signed s n : Rat) / ((unit : Int) : Rat) := by
  cases s <;> simp [toRatD, toRat, signed, Int.cast_neg]

theorem toRat_fin_mul_unit (s : Bool) (k : Nat) :
    (fin s (k * unit)).toRatD = ((signed s k : Int) : Rat) := by
  have c : ((unit : Int) : Rat) ≠ 0 :=
    ne_of_gt (Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos))
  rw [toRat_fin]
  have hs : signed s (k * unit) = signed s k * (unit : Int) := by
    cases s
    · rw [signed_false, signed_false, Nat.cast_mul]
    · rw [signed_true, signed_true, Nat.cast_mul, neg_mul]
  rw [hs, Int.cast_mul, mul_div_assoc, div_self c, mul_one]

/-- `fin false (K·unit)` has value `K`, so a `toRat` bound of `K` translates to
a magnitude bound of `K·unit` via `mag_le_of_toRatD_le`. -/
theorem const_mag (K : Nat) : (fin false (K * unit)).toRatD = K := by
  have c : ((unit : Nat) : Rat) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt unit_pos)
  rw [toRat_fin]
  simp only [signed_false, Nat.cast_mul, Int.cast_mul,
    Int.cast_natCast (R := Rat), mul_div_assoc]
  rw [div_self c, mul_one]

/-- `Math.round` keeps the sign and only adds at most `unit` to the
magnitude. -/
theorem jsround_fin_le {neg : Bool} {n : Nat} :
    ∃ m, (fin neg n).jsround = fin neg m ∧ m ≤ n + unit := by
  rw [jsround_fin]
  by_cases h1 : n % unit * 2 < unit
  · rw [ite_eq_left h1]
    exact ⟨n / unit * unit, rfl,
      le_trans (Nat.div_mul_le_self n unit) (Nat.le_add_right n unit)⟩
  · rw [ite_eq_right h1]
    by_cases h2 : n % unit * 2 = unit
    · rw [ite_eq_left h2]
      refine ⟨(n / unit + (if neg then 0 else 1)) * unit, rfl, ?_⟩
      have hq : n / unit * unit ≤ n := Nat.div_mul_le_self n unit
      have h3 : n / unit + (if neg then 0 else 1) ≤ n / unit + 1 := by
        cases neg <;> simp
      calc (n / unit + (if neg then 0 else 1)) * unit
          ≤ (n / unit + 1) * unit := Nat.mul_le_mul_right _ h3
        _ = n / unit * unit + unit := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ n + unit := by omega
    · rw [ite_eq_right h2]
      refine ⟨(n / unit + 1) * unit, rfl, ?_⟩
      have hq : n / unit * unit ≤ n := Nat.div_mul_le_self n unit
      rw [Nat.add_mul, Nat.one_mul]
      omega


theorem lt_iff {x y : F64} (hx : x.isFin = true) (hy : y.isFin = true) :
    x.lt y = true ↔ x.toRatD < y.toRatD := by
  cases x <;> simp [isFin] at hx
  cases y <;> simp [isFin] at hy
  rename_i a n b m
  simp only [lt, toRat_fin, decide_eq_true_eq]
  have c : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  rw [div_lt_div_iff_of_pos_right c]
  exact (Int.cast_lt (R := Rat)).symm

theorem eq_iff {x y : F64} (hx : x.isFin = true) (hy : y.isFin = true) :
    x.eq y = true ↔ x.toRatD = y.toRatD := by
  cases x <;> simp [isFin] at hx
  cases y <;> simp [isFin] at hy
  rename_i a n b m
  simp only [eq, le.eq', decide_eq_true_eq, toRat_fin]
  have c : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  rw [div_eq_div_iff c.ne' c.ne']
  constructor
  · intro h; rw [h]
  · intro h
    exact Int.cast_inj.mp (mul_right_cancel₀ c.ne' h)
/-- `0 ≤ toRatD` on a finite value says the sign is `false` or the value is `0`. -/
theorem toRat_nonneg_iff {s : Bool} {n : Nat} :
    (0 ≤ (fin s n).toRatD) ↔ s = false ∨ n = 0 := by
  simp only [toRat_fin]
  have c : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  have key : (0 ≤ (signed s n : Rat) / ((unit : Int) : Rat)) ↔ (0 : Rat) ≤ signed s n := by
    constructor
    · intro h
      have h2 := mul_nonneg h (le_of_lt c)
      rwa [div_mul_cancel₀ _ c.ne'] at h2
    · intro h; exact div_nonneg h (by positivity)
  rw [key]
  cases s <;> simp [signed]

/-- `round` keeps its sign argument in the `fin` it returns. -/
theorem round_sign {neg : Bool} {n e : Nat} {st : Bool} {s : Bool} {m : Nat}
    (h : round neg n e st = fin s m) : s = neg := by
  simp only [round] at h
  split_ifs at h <;> simp_all

/-- The `fin` a `round` call returns keeps `toRatD` non-negative when its sign
is `false`, and lands exactly on `0` when the magnitude is `0`. -/
theorem round_toRat_nonneg (neg : Bool) (n e : Nat) (st : Bool)
    (h : n = 0 ∨ neg = false) : 0 ≤ (round neg n e st).toRatD := by
  rcases h with h | h
  · subst h
    simp only [round, ↓reduceIte]
    cases neg <;> simp [toRatD, toRat]
  · subst h
    generalize hz : round false n e st = z
    cases z <;> simp [toRatD, toRat]
    rename_i s m
    have hs := round_sign hz
    subst hs
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)

private theorem signed_nonneg_of_toRat {s : Bool} {n : Nat}
    (h : 0 ≤ (fin s n).toRatD) : 0 ≤ signed s n := by
  rw [toRat_fin] at h
  have c : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  have h2 := mul_nonneg h (le_of_lt c)
  rw [div_mul_cancel₀ _ c.ne'] at h2
  exact_mod_cast h2

/-- `x + y` of non-negative finite inputs is non-negative (or `±∞`/`NaN`, which
`toRatD` reads as `0`). -/
theorem add_toRat_nonneg {x y : F64} (hx : 0 ≤ x.toRatD) (hy : 0 ≤ y.toRatD) :
    0 ≤ (x.add y).toRatD := by
  cases x
  · cases y <;> simp [add, toRatD, toRat]
  · rename_i a
    cases y
    · simp [add, toRatD, toRat]
    · rename_i b
      simp only [add]
      split <;> simp [toRatD, toRat]
    · rename_i b m
      simp [add, toRatD, toRat]
  · rename_i a n
    cases y
    · simp [add, toRatD, toRat]
    · rename_i b
      simp [add, toRatD, toRat]
    · rename_i b m
      have ha := signed_nonneg_of_toRat hx
      have hb := signed_nonneg_of_toRat hy
      have hr : 0 ≤ signed a n + signed b m := Int.add_nonneg ha hb
      simp only [add]
      split
      · cases a <;> cases b <;> simp [toRatD, toRat]
      · rename_i hne
        have hd : decide (signed a n + signed b m < 0) = false := by
          rw [decide_eq_false]; omega
        rw [hd]
        exact round_toRat_nonneg false _ 0 false (Or.inr rfl)

/-- `x * y` of non-negative finite inputs is non-negative (or `±∞`/`NaN`). -/
theorem mul_toRat_nonneg {x y : F64} (hx : 0 ≤ x.toRatD) (hy : 0 ≤ y.toRatD) :
    0 ≤ (x.mul y).toRatD := by
  cases x
  · cases y <;> simp [mul, toRatD, toRat]
  · rename_i a
    cases y
    · simp [mul, toRatD, toRat]
    · rename_i b
      simp [mul, toRatD, toRat]
    · rename_i b m
      simp only [mul]
      split <;> simp [toRatD, toRat]
  · rename_i a n
    cases y
    · simp [mul, toRatD, toRat]
    · rename_i b
      simp only [mul]
      split <;> simp [toRatD, toRat]
    · rename_i b m
      have ha := signed_nonneg_of_toRat hx
      have hb := signed_nonneg_of_toRat hy
      simp only [mul]
      by_cases hnm : n * m = 0
      · exact round_toRat_nonneg (a != b) _ _ _ (Or.inl hnm)
      · have hn : n ≠ 0 := fun h => hnm (by simp [h])
        have hm : m ≠ 0 := fun h => hnm (by simp [h])
        have ha' : a = false := by
          cases a
          · rfl
          · simp only [signed, ↓reduceIte] at ha
            exfalso; omega
        have hb' : b = false := by
          cases b
          · rfl
          · simp only [signed, ↓reduceIte] at hb
            exfalso; omega
        rw [ha', hb']
        exact round_toRat_nonneg false _ _ _ (Or.inr rfl)

/-- `x / y` of non-negative finite inputs is non-negative (or `±∞`/`NaN`). -/
theorem div_toRat_nonneg {x y : F64} (hx : 0 ≤ x.toRatD) (hy : 0 ≤ y.toRatD) :
    0 ≤ (x.div y).toRatD := by
  cases x
  · cases y <;> simp [div, toRatD, toRat]
  · rename_i a
    cases y
    · simp [div, toRatD, toRat]
    · rename_i b
      simp [div, toRatD, toRat]
    · rename_i b m
      simp [div, toRatD, toRat]
  · rename_i a n
    cases y
    · simp [div, toRatD, toRat]
    · rename_i b
      simp [div, toRatD, toRat]
    · rename_i b m
      have ha := signed_nonneg_of_toRat hx
      have hb := signed_nonneg_of_toRat hy
      simp only [div]
      split
      · split <;> simp [toRatD, toRat]
      · split
        · cases a <;> cases b <;> simp [toRatD, toRat]
        · rename_i hm hn
          have ha' : a = false := by
            cases a
            · rfl
            · simp only [signed, ↓reduceIte] at ha
              exfalso; omega
          have hb' : b = false := by
            cases b
            · rfl
            · simp only [signed, ↓reduceIte] at hb
              exfalso; omega
          rw [ha', hb']
          exact round_toRat_nonneg false _ _ _ (Or.inr rfl)

/-- `Math.round` always lands on a whole number of `unit`s. -/
theorem jsround_isInt {x : F64} (hx : x.isFin = true) :
    (x.jsround).isInt' = true := by
  cases x <;> simp [isFin] at hx
  rename_i neg n
  simp only [jsround]
  split_ifs <;> simp [isInt']

/-- `Math.floor` never exceeds its argument. -/
theorem floor_le_toRat {x : F64} (hx : x.isFin = true) :
    (x.floor).toRatD ≤ x.toRatD := by
  cases x <;> simp [isFin] at hx
  rename_i s n
  simp only [toRat_fin]
  have c : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  have hde : n = (n / unit) * unit + n % unit := by
    rw [Nat.mul_comm (n / unit) unit]; exact (Nat.div_add_mod _ _).symm
  have hrl : n % unit < unit := Nat.mod_lt _ unit_pos
  cases s
  · rw [floor_fin_false]
    rw [toRat_fin, div_le_div_iff_of_pos_right c]
    simp only [signed_false, Nat.cast_mul]
    exact Int.cast_le.mpr (by omega)
  · rw [floor_fin_true]
    split_ifs with h
    · rw [toRat_fin]
    · simp only [toRat_fin]
      rw [div_le_div_iff_of_pos_right c]
      apply Int.cast_le.mpr
      rw [signed_true, signed_true, Nat.cast_mul, Nat.cast_add, add_mul]
      simp only [Nat.cast_one, one_mul]
      omega

/-- `Math.ceil` never goes below its argument. -/
theorem toRat_le_ceil {x : F64} (hx : x.isFin = true) :
    x.toRatD ≤ (x.ceil).toRatD := by
  cases x <;> simp [isFin] at hx
  rename_i s n
  simp only [toRat_fin]
  have c : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  have hde : n = (n / unit) * unit + n % unit := by
    rw [Nat.mul_comm (n / unit) unit]; exact (Nat.div_add_mod _ _).symm
  have hrl : n % unit < unit := Nat.mod_lt _ unit_pos
  cases s
  · rw [ceil_fin_false]
    split_ifs with h
    · rw [toRat_fin]
    · simp only [toRat_fin]
      rw [div_le_div_iff_of_pos_right c]
      apply Int.cast_le.mpr
      rw [signed_false, signed_false, Nat.cast_mul, Nat.cast_add, add_mul]
      simp only [Nat.cast_one, one_mul]
      omega
  · rw [ceil_fin_true]
    split_ifs with h
    · simp only [toRat_fin]
      rw [div_le_div_iff_of_pos_right c]
      apply Int.cast_le.mpr
      rw [signed_true, signed_true, Nat.cast_zero]
      omega
    · simp only [toRat_fin]
      rw [div_le_div_iff_of_pos_right c]
      apply Int.cast_le.mpr
      rw [signed_true, signed_true, Nat.cast_mul]
      omega

/-- `trunc`/`floor`/`ceil`/`Math.round`/`abs`/`neg` keep finiteness. -/
theorem isFin_trunc {x : F64} : (x.trunc).isFin = x.isFin := by
  cases x <;> rfl

theorem isFin_floor {x : F64} : (x.floor).isFin = x.isFin := by
  cases x <;> try rfl
  rename_i s n
  cases s
  · rfl
  · simp only [floor]; split_ifs <;> simp [isFin]

theorem isFin_ceil {x : F64} : (x.ceil).isFin = x.isFin := by
  cases x <;> try rfl
  rename_i s n
  cases s <;> simp only [ceil] <;> try split_ifs <;> simp [isFin]

theorem isFin_jsround {x : F64} : (x.jsround).isFin = x.isFin := by
  cases x <;> try rfl
  rename_i s n
  simp only [jsround]
  split_ifs <;> simp [isFin]

theorem isFin_neg {x : F64} : (x.neg).isFin = x.isFin := by
  cases x <;> rfl

theorem isFin_abs {x : F64} : (x.abs).isFin = x.isFin := by
  cases x <;> rfl

/-- `toRatD (floor x)` is `toRatD x` floored to an integer: the integer part of
`signed s n` after factoring out `unit`, i.e. `n / unit` for positives and
`⌈n / unit⌉` (negated) for negatives. -/
theorem floor_toRat {s : Bool} {n : Nat} :
    (fin s n).floor.toRatD = ((signed s (magUnit s n) : Int) : Rat) := by
  cases s
  · rw [floor_fin_false, magUnit_false]
    exact toRat_fin_mul_unit false (n / unit)
  · rw [floor_fin_true]
    split_ifs with h
    · rw [magUnit_true_of_mod h]
      have e : fin true n = fin true (n / unit * unit) :=
        congrArg (fin true) (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm
      rw [e]
      exact toRat_fin_mul_unit true (n / unit)
    · rw [magUnit_true_of_mod_ne h]
      exact toRat_fin_mul_unit true (n / unit + 1)

private theorem toRat_sub_bound (s : Bool) (K n : Nat)
    (hK : |signed s K - signed s n| ≤ (unit : Int) / 2) :
    |(fin s K).toRatD - (fin s n).toRatD| ≤ (1 : Rat) / 2 := by
  have c : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  have hdiv : (2 : Int) * 2 ^ 1073 = (unit : Int) := by
    exact_mod_cast (by unfold unit; ring)
  have hD2 : (2 : Int) ∣ (unit : Int) := ⟨2 ^ 1073, hdiv.symm⟩
  have e : (1 / 2 : Rat) * ((unit : Int) : Rat) = (((unit : Int) / 2 : Int) : Rat) := by
    rw [mul_comm, mul_one_div]
    first
      | norm_cast
  have en : (-(1 / 2 : Rat)) * ((unit : Int) : Rat) = -(((unit : Int) / 2 : Int) : Rat) := by
    rw [show (-(1 / 2 : Rat)) * ((unit : Int) : Rat) =
          -((1 / 2 : Rat) * ((unit : Int) : Rat)) from by ring, e]
  rw [toRat_fin s K, toRat_fin s n, ← sub_div, ← Int.cast_sub]
  rw [abs_le] at hK
  rw [abs_le]
  obtain ⟨hL, hR⟩ := hK
  constructor
  · rw [le_div_iff₀ c, en, ← Int.cast_neg]
    exact Int.cast_le.mpr hL
  · rw [div_le_iff₀ c, e]
    exact Int.cast_le.mpr hR


/-- `Math.round` lands within half a `unit` of its argument. -/
theorem jsround_err_half {x : F64} (hx : x.isFin = true) :
    |(x.jsround).toRatD - x.toRatD| ≤ (1 : Rat) / 2 := by
  cases x <;> simp [isFin] at hx
  rename_i s n
  have hde : n = (n / unit) * unit + n % unit := by
    rw [Nat.mul_comm (n / unit) unit]; exact (Nat.div_add_mod _ _).symm
  have hrl : n % unit < unit := Nat.mod_lt _ unit_pos
  cases s
  · rw [jsround_fin]
    simp only [Bool.false_eq_true, ite_false]
    split_ifs with hlt hte
    · have hK : -(↑unit / 2 : Int) ≤ signed false (n / unit * unit) - signed false n ∧
          signed false (n / unit * unit) - signed false n ≤ ↑unit / 2 := by
        rw [signed_false, signed_false, Nat.cast_mul]
        omega
      exact toRat_sub_bound false _ n (abs_le.mpr hK)
    · have hK : -(↑unit / 2 : Int) ≤
          signed false ((n / unit + 1) * unit) - signed false n ∧
          signed false ((n / unit + 1) * unit) - signed false n ≤ ↑unit / 2 := by
        rw [signed_false, signed_false, Nat.cast_mul, Nat.cast_add, add_mul]
        simp only [Nat.cast_one, one_mul]
        omega
      exact toRat_sub_bound false _ n (abs_le.mpr hK)
    · have hgtN : unit < n % unit * 2 :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (fun h => hte h.symm)
      have hK : -(↑unit / 2 : Int) ≤
          signed false ((n / unit + 1) * unit) - signed false n ∧
          signed false ((n / unit + 1) * unit) - signed false n ≤ ↑unit / 2 := by
        rw [signed_false, signed_false, Nat.cast_mul, Nat.cast_add, add_mul]
        simp only [Nat.cast_one, one_mul]
        omega
      exact toRat_sub_bound false _ n (abs_le.mpr hK)
  · rw [jsround_fin]
    simp only [eq_self, ite_true]
    split_ifs with hlt hte
    · have hK : -(↑unit / 2 : Int) ≤ signed true (n / unit * unit) - signed true n ∧
          signed true (n / unit * unit) - signed true n ≤ ↑unit / 2 := by
        rw [signed_true, signed_true, Nat.cast_mul]
        omega
      exact toRat_sub_bound true _ n (abs_le.mpr hK)
    · have hK : -(↑unit / 2 : Int) ≤
          signed true ((n / unit + 0) * unit) - signed true n ∧
          signed true ((n / unit + 0) * unit) - signed true n ≤ ↑unit / 2 := by
        rw [signed_true, signed_true, Nat.cast_mul, Nat.cast_add, add_mul]
        simp only [Nat.cast_zero]
        omega
      exact toRat_sub_bound true _ n (abs_le.mpr hK)
    · have hgtN : unit < n % unit * 2 :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (fun h => hte h.symm)
      have hK : -(↑unit / 2 : Int) ≤
          signed true ((n / unit + 1) * unit) - signed true n ∧
          signed true ((n / unit + 1) * unit) - signed true n ≤ ↑unit / 2 := by
        rw [signed_true, signed_true, Nat.cast_mul, Nat.cast_add, add_mul]
        simp only [Nat.cast_one, one_mul]
        omega
      exact toRat_sub_bound true _ n (abs_le.mpr hK)
theorem le_iff {x y : F64} (hx : x.isFin = true) (hy : y.isFin = true) :
    x.le y = true ↔ x.toRatD ≤ y.toRatD := by
  rw [le, Bool.or_eq_true_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact ((lt_iff hx hy).mp h).le
    · exact (eq_iff hx hy).mp h |>.le
  · intro h
    rcases h.eq_or_lt with he | hl
    · exact Or.inr ((eq_iff hx hy).mpr he)
    · exact Or.inl ((lt_iff hx hy).mpr hl)
private theorem floor_mag_le {a b : Bool} {n m : Nat}
    (h : signed a n ≤ signed b m) :
    signed a (magUnit a n) ≤ signed b (magUnit b m) := by
  have hdeN : n = (n / unit) * unit + n % unit := by
    rw [Nat.mul_comm (n / unit) unit]; exact (Nat.div_add_mod _ _).symm
  have hrlN : n % unit < unit := Nat.mod_lt _ unit_pos
  have hdeM : m = (m / unit) * unit + m % unit := by
    rw [Nat.mul_comm (m / unit) unit]; exact (Nat.div_add_mod _ _).symm
  have hrlM : m % unit < unit := Nat.mod_lt _ unit_pos
  have hup := unit_pos
  cases a <;> cases b
  · rw [magUnit_false, magUnit_false]
    simp only [signed_false] at h ⊢
    exact Nat.cast_le.mpr (Nat.div_le_div_right (Nat.cast_le.mp h))
  · rw [magUnit_false]
    simp only [signed_false, signed_true] at h ⊢
    have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst hn; subst hm
    rw [magUnit_true_of_mod (by simp)]
    simp only [Nat.zero_div, Nat.cast_zero]
    omega
  · by_cases h0 : n % unit = 0
    · rw [magUnit_true_of_mod h0, magUnit_false]
      simp only [signed_true, signed_false] at h ⊢
      have q0 : (0 : Int) ≤ (↑n : Int) / (↑unit : Int) :=
        Int.ediv_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have q1 : (0 : Int) ≤ (↑m : Int) / (↑unit : Int) :=
        Int.ediv_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      omega
    · rw [magUnit_true_of_mod_ne h0, magUnit_false]
      simp only [signed_true, signed_false] at h ⊢
      have q0 : (0 : Int) ≤ (↑n : Int) / (↑unit : Int) :=
        Int.ediv_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have q1 : (0 : Int) ≤ (↑m : Int) / (↑unit : Int) :=
        Int.ediv_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      omega
  · simp only [signed_true] at h ⊢
    have hnm : m ≤ n := by omega
    by_cases h0 : n % unit = 0
    · by_cases h1 : m % unit = 0
      · rw [magUnit_true_of_mod h0, magUnit_true_of_mod h1]
        exact neg_le_neg (Nat.cast_le.mpr (Nat.div_le_div_right hnm))
      · rw [magUnit_true_of_mod h0, magUnit_true_of_mod_ne h1]
        simp only [Nat.cast_add]
        have hne : m ≠ n := by rintro rfl; omega
        have hlt : m < n := Nat.lt_of_le_of_ne hnm hne
        have hq : m / unit + 1 ≤ n / unit :=
          Nat.div_lt_div_of_lt_of_dvd (Nat.dvd_of_mod_eq_zero h0) hlt
        omega
    · by_cases h1 : m % unit = 0
      · rw [magUnit_true_of_mod_ne h0, magUnit_true_of_mod h1]
        simp only [Nat.cast_add]
        have hq : m / unit ≤ n / unit := Nat.div_le_div_right hnm
        omega
      · rw [magUnit_true_of_mod_ne h0, magUnit_true_of_mod_ne h1]
        exact neg_le_neg (Nat.cast_le.mpr
          (Nat.add_le_add_right (Nat.div_le_div_right hnm) 1))

/-- `Math.ceil` of a finite value, as a rational. -/
theorem ceil_toRat {s : Bool} {n : Nat} :
    (fin s n).ceil.toRatD = ((signed s (magUnit (!s) n) : Int) : Rat) := by
  cases s
  · change (fin false n).ceil.toRatD = ((signed false (magUnit true n) : Int) : Rat)
    rw [ceil_fin_false]
    split_ifs with h
    · rw [magUnit_true_of_mod h]
      have e : fin false n = fin false (n / unit * unit) :=
        congrArg (fin false) (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm
      rw [e]
      exact toRat_fin_mul_unit false (n / unit)
    · rw [magUnit_true_of_mod_ne h]
      exact toRat_fin_mul_unit false (n / unit + 1)
  · change (fin true n).ceil.toRatD = ((signed true (magUnit false n) : Int) : Rat)
    rw [ceil_fin_true]
    by_cases h : n / unit = 0
    · rw [ite_eq_left h, magUnit_false, h, toRat_fin, signed_true]
      simp
    · rw [ite_eq_right h, magUnit_false]
      exact toRat_fin_mul_unit true (n / unit)

private theorem signed_le_of_toRat_le {a b : Bool} {n m : Nat}
    (h : (fin a n).toRatD ≤ (fin b m).toRatD) : signed a n ≤ signed b m := by
  rw [toRat_fin, toRat_fin] at h
  have c : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  rw [div_le_iff₀ c, div_mul_cancel₀ _ (ne_of_gt c)] at h
  exact Int.cast_le.mp h

/-- `Math.floor` is monotone: `x ≤ y` implies `⌊x⌋ ≤ ⌊y⌋`. -/
theorem floor_mono {x y : F64} (hx : x.isFin = true) (hy : y.isFin = true)
    (h : x.toRatD ≤ y.toRatD) : (x.floor).toRatD ≤ (y.floor).toRatD := by
  cases x <;> simp [isFin] at hx
  cases y <;> simp [isFin] at hy
  rename_i a n b m
  rw [floor_toRat, floor_toRat]
  exact Int.cast_le.mpr (floor_mag_le (signed_le_of_toRat_le h))

private theorem ceil_mag_le {a b : Bool} {n m : Nat}
    (h : signed a n ≤ signed b m) :
    signed a (magUnit (!a) n) ≤ signed b (magUnit (!b) m) := by
  cases a <;> cases b
  · change signed false (magUnit true n) ≤ signed false (magUnit true m)
    simp only [signed_false] at h ⊢
    have hnm : n ≤ m := Nat.cast_le.mp h
    by_cases h0 : n % unit = 0
    · rw [magUnit_true_of_mod h0]
      by_cases h1 : m % unit = 0
      · rw [magUnit_true_of_mod h1]
        exact Nat.cast_le.mpr (Nat.div_le_div_right hnm)
      · rw [magUnit_true_of_mod_ne h1]
        have hq : n / unit ≤ m / unit + 1 :=
          Nat.le_trans (Nat.div_le_div_right hnm) (Nat.le_succ _)
        exact Nat.cast_le.mpr hq
    · rw [magUnit_true_of_mod_ne h0]
      by_cases h1 : m % unit = 0
      · rw [magUnit_true_of_mod h1]
        have hlt : n < m := Nat.lt_of_le_of_ne hnm (fun hn => h0 (hn ▸ h1))
        have hq : n / unit + 1 ≤ m / unit :=
          Nat.div_lt_div_of_lt_of_dvd (Nat.dvd_of_mod_eq_zero h1) hlt
        exact Nat.cast_le.mpr hq
      · rw [magUnit_true_of_mod_ne h1]
        exact Nat.cast_le.mpr (Nat.add_le_add_right (Nat.div_le_div_right hnm) 1)
  · simp only [signed_false, signed_true] at h
    have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst hn; subst hm
    decide
  · change signed true (magUnit false n) ≤ signed false (magUnit true m)
    rw [magUnit_false]
    simp only [signed_true, signed_false] at h ⊢
    exact le_trans (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · change signed true (magUnit false n) ≤ signed true (magUnit false m)
    rw [magUnit_false, magUnit_false]
    simp only [signed_true] at h ⊢
    have hnm : m ≤ n := by omega
    exact neg_le_neg (Nat.cast_le.mpr (Nat.div_le_div_right hnm))

private theorem mul_pow_le_of_mul_pow_le {r m n s e : Nat} (hse : e ≤ s)
    (hs0 : 0 < s) (hsle : s ≤ e + 1074) (hn : n ≤ 2 ^ (1074 + e))
    (h : m * 2 ^ s ≤ n + 2 ^ (s - 1)) (hr : r * 2 ^ e = m * 2 ^ s) :
    r ≤ 2 ^ 1074 := by
  have hbound : r * 2 ^ e < 2 ^ (1074 + e) + 2 ^ s := by
    have h1 : m * 2 ^ s ≤ 2 ^ (1074 + e) + 2 ^ (s - 1) :=
      le_trans h (Nat.add_le_add_right hn _)
    have h2 : 2 ^ (s - 1) < 2 ^ s := by
      apply Nat.pow_lt_pow_right (by decide : 1 < (2:Nat))
      omega
    rw [hr]
    exact lt_of_le_of_lt h1 (Nat.add_lt_add_left h2 _)
  by_cases hseq : s = e
  · have hlt : r * 2 ^ e < (2 ^ 1074 + 1) * 2 ^ e := by
      have e1 : (2 ^ 1074 + 1) * 2 ^ e = 2 ^ (1074 + e) + 2 ^ e := by
        rw [Nat.add_mul, one_mul, ← Nat.pow_add]
      rw [e1]
      have h2 : 2 ^ (s - 1) < 2 ^ e := by
        apply Nat.pow_lt_pow_right (by decide : 1 < (2:Nat))
        omega
      exact lt_of_lt_of_le hbound (by rw [← hseq])
    have hlt2 : r < 2 ^ 1074 + 1 := Nat.lt_of_mul_lt_mul_right hlt
    omega
  · have d : s - e ≤ 1074 := by omega
    have hsplit : (2 ^ 1074 + 2 ^ (s - e)) * 2 ^ e = 2 ^ (1074 + e) + 2 ^ s := by
      rw [Nat.add_mul, ← Nat.pow_add, ← Nat.pow_add, Nat.sub_add_cancel hse]
    have hlt : r * 2 ^ e < (2 ^ 1074 + 2 ^ (s - e)) * 2 ^ e := by
      rw [hsplit]; exact hbound
    have hlt2 : r < 2 ^ 1074 + 2 ^ (s - e) := Nat.lt_of_mul_lt_mul_right hlt
    have hrm' : r = m * 2 ^ (s - e) := by
      have hh : r * 2 ^ e = m * 2 ^ (s - e) * 2 ^ e := by
        rw [hr, Nat.mul_assoc, ← Nat.pow_add, show s - e + e = s from by omega]
      exact Nat.eq_of_mul_eq_mul_right (pow_pos (by decide : 0 < (2:Nat)) e) hh
    have huc : 2 ^ 1074 = 2 ^ (1074 - (s - e)) * 2 ^ (s - e) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hrm', huc] at hlt2
    rw [hrm']
    have hmc : m ≤ 2 ^ (1074 - (s - e)) := by
      have hadd : 2 ^ (1074 - (s - e)) * 2 ^ (s - e) + 2 ^ (s - e) =
          (2 ^ (1074 - (s - e)) + 1) * 2 ^ (s - e) := by
        rw [Nat.add_mul, one_mul]
      rw [hadd] at hlt2
      have hh := Nat.lt_of_mul_lt_mul_right hlt2
      omega
    calc m * 2 ^ (s - e) ≤ 2 ^ (1074 - (s - e)) * 2 ^ (s - e) := by
          exact Nat.mul_le_mul hmc (le_refl _)
      _ = 2 ^ 1074 := huc.symm
theorem round_le_unit {sgn : Bool} {n e : Nat} {st : Bool}
    (hn : n ≤ 2 ^ (1074 + e)) : (round sgn n e st).toRatD ≤ 1 := by
  simp only [round]
  generalize hs : max (n.log2 + 1 - 53) e = s
  split_ifs with h0 hS hlim hup hlim2
  · simp [toRatD, toRat]
  · simp [toRatD, toRat]
  · have he0 : e = 0 := by
      have h := Nat.le_max_right (n.log2 + 1 - 53) e; omega
    subst he0
    have hn' : n ≤ unit := hn
    rw [toRat_fin]
    have c : (0 : Rat) < ((unit : Int) : Rat) :=
      Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
    cases sgn
    · simp only [signed_false]
      rw [div_le_iff₀ c, one_mul]
      exact_mod_cast hn'
    · simp only [signed_true]
      apply le_trans _ zero_le_one
      apply div_nonpos_of_nonpos_of_nonneg
      · exact Int.cast_nonpos.mpr (neg_nonpos.mpr (Int.natCast_nonneg _))
      · exact le_of_lt c
  · simp [toRatD, toRat]
  · rw [toRat_fin]
    have c : (0 : Rat) < ((unit : Int) : Rat) :=
      Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
    have hse : e ≤ s := by
      have h := Nat.le_max_right (n.log2 + 1 - 53) e; omega
    have hs0 : 0 < s := by omega
    have hlog : n.log2 ≤ 1074 + e := by
      have hlt := Nat.log2_lt h0 |>.mpr
        (Nat.lt_of_le_of_lt hn (Nat.pow_lt_pow_right (by decide : 1 < (2:Nat)) (Nat.lt_succ_self _)))
      omega
    have hsle : s ≤ e + 1074 := by
      rcases lt_or_ge e (n.log2 + 1 - 53) with h | h
      · rw [Nat.max_eq_left (le_of_lt h)] at hs; omega
      · rw [Nat.max_eq_right h] at hs; omega
    have hhalf : 2 ^ (s - 1) ≤ n % 2 ^ s := by
      rcases (Bool.or_eq_true _ _).mp hup with h1 | h2
      · exact le_of_lt (of_decide_eq_true h1)
      · exact le_of_eq (of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h2 |>.1)).symm
    have h2s : 2 ^ s = 2 * 2 ^ (s - 1) := by
      rw [Nat.mul_comm, ← pow_succ, show s - 1 + 1 = s from by omega]
    have hke : n / 2 ^ s * 2 ^ s + n % 2 ^ s = n := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have hrl : n % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
    have hbound : (n / 2 ^ s + 1) * 2 ^ s ≤ n + 2 ^ (s - 1) := by
      rw [Nat.add_mul, one_mul]
      omega
    have hr : (n / 2 ^ s + 1) * 2 ^ (s - e) * 2 ^ e = (n / 2 ^ s + 1) * 2 ^ s := by
      rw [Nat.mul_assoc, ← Nat.pow_add, show s - e + e = s from by omega]
    have hru : (n / 2 ^ s + 1) * 2 ^ (s - e) ≤ unit :=
      mul_pow_le_of_mul_pow_le hse hs0 hsle hn hbound hr
    cases sgn
    · simp only [signed_false]
      rw [div_le_iff₀ c, one_mul]
      exact_mod_cast hru
    · simp only [signed_true]
      apply le_trans _ zero_le_one
      apply div_nonpos_of_nonpos_of_nonneg
      · exact Int.cast_nonpos.mpr (neg_nonpos.mpr (Int.natCast_nonneg _))
      · exact le_of_lt c
  · simp [toRatD, toRat]
  · rw [toRat_fin]
    have c : (0 : Rat) < ((unit : Int) : Rat) :=
      Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
    have hse : e ≤ s := by
      have h := Nat.le_max_right (n.log2 + 1 - 53) e; omega
    have hs0 : 0 < s := by omega
    have hlog : n.log2 ≤ 1074 + e := by
      have hlt := Nat.log2_lt h0 |>.mpr
        (Nat.lt_of_le_of_lt hn (Nat.pow_lt_pow_right (by decide : 1 < (2:Nat)) (Nat.lt_succ_self _)))
      omega
    have hsle : s ≤ e + 1074 := by
      rcases lt_or_ge e (n.log2 + 1 - 53) with h | h
      · rw [Nat.max_eq_left (le_of_lt h)] at hs; omega
      · rw [Nat.max_eq_right h] at hs; omega
    have hke : n / 2 ^ s * 2 ^ s + n % 2 ^ s = n := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
    have hbound : (n / 2 ^ s) * 2 ^ s ≤ n + 2 ^ (s - 1) := by
      calc (n / 2 ^ s) * 2 ^ s ≤ n := by
            conv => rhs; rw [← hke]
            exact Nat.le_add_right _ _
        _ ≤ n + 2 ^ (s - 1) := Nat.le_add_right _ _
    have hr : (n / 2 ^ s) * 2 ^ (s - e) * 2 ^ e = (n / 2 ^ s) * 2 ^ s := by
      rw [Nat.mul_assoc, ← Nat.pow_add, show s - e + e = s from by omega]
    have hru : (n / 2 ^ s) * 2 ^ (s - e) ≤ unit :=
      mul_pow_le_of_mul_pow_le hse hs0 hsle hn hbound hr
    cases sgn
    · simp only [signed_false]
      rw [div_le_iff₀ c, one_mul]
      exact_mod_cast hru
    · simp only [signed_true]
      apply le_trans _ zero_le_one
      apply div_nonpos_of_nonpos_of_nonneg
      · exact Int.cast_nonpos.mpr (neg_nonpos.mpr (Int.natCast_nonneg _))
      · exact le_of_lt c

/-- `Math.ceil` is monotone: `x ≤ y` implies `⌈x⌉ ≤ ⌈y⌉`. -/
theorem ceil_mono {x y : F64} (hx : x.isFin = true) (hy : y.isFin = true)
    (h : x.toRatD ≤ y.toRatD) : (x.ceil).toRatD ≤ (y.ceil).toRatD := by
  cases x <;> simp [isFin] at hx
  cases y <;> simp [isFin] at hy
  rename_i a n b m
  rw [ceil_toRat, ceil_toRat]
  exact Int.cast_le.mpr (ceil_mag_le (signed_le_of_toRat_le h))

theorem sub_toRat_nonneg {a b : Bool} {X Y : Nat}
    (_hx : 0 ≤ signed a X) (hle : signed b Y ≤ signed a X) :
    0 ≤ ((fin a X).sub (fin b Y)).toRatD := by
  have hnb : signed (!b) Y = -signed b Y := by cases b <;> simp [signed]
  have hr : 0 ≤ signed a X + signed (!b) Y := by rw [hnb]; omega
  simp only [sub, add, neg]
  set r := signed a X + signed (!b) Y
  split_ifs with h0
  · simp [toRatD, toRat]
  · have hd : decide (r < 0) = false := decide_eq_false (by omega : ¬(r < 0))
    rw [hd]
    exact round_toRat_nonneg false r.natAbs 0 false (Or.inr rfl)

theorem jsround_toRat_nonneg {s : Bool} {n : Nat} (h : s = false ∨ n = 0) :
    0 ≤ ((fin s n).jsround).toRatD := by
  rw [jsround_fin]
  have hu : 0 < unit := unit_pos
  split_ifs with h1 h2
  · rw [toRat_nonneg_iff]
    rcases h with h | h
    · exact Or.inl h
    · right; rw [h]; simp
  · rw [toRat_nonneg_iff]
    rcases h with h | h
    · exact Or.inl h
    · rw [h, Nat.zero_mod] at h2; omega
  · rw [toRat_nonneg_iff]
    rcases h with h | h
    · exact Or.inl h
    · rw [h, Nat.zero_mod] at h2; omega
  · rw [toRat_nonneg_iff]
    rcases h with h | h
    · exact Or.inl h
    · rw [h] at h1
      simp only [Nat.zero_mod] at h1
      omega

theorem div_le_unit {a b : Bool} {X Y : Nat} (hle : X ≤ Y) :
    ((fin a X).div (fin b Y)).toRatD ≤ 1 := by
  simp only [div]
  generalize hL : Nat.log2 Y = L
  by_cases hY0 : Y = 0
  · rw [ite_eq_left hY0]
    split_ifs <;> simp [toRatD, toRat]
  · rw [ite_eq_right hY0]
    by_cases hX0 : X = 0
    · rw [ite_eq_left hX0]; simp [toRatD, toRat]
    · rw [ite_eq_right hX0]
      apply round_le_unit
      have htop : X * 2 ^ (1074 + (L + 64)) ≤ Y * 2 ^ (1074 + (L + 64)) :=
        Nat.mul_le_mul_right _ hle
      exact Nat.div_le_of_le_mul htop

theorem sub_toRat_nonneg' {x y : F64} (hx : 0 ≤ x.toRatD) (hle : y.toRatD ≤ x.toRatD) :
    0 ≤ (x.sub y).toRatD := by
  cases x with
  | fin a X =>
    cases y with
    | fin b Y =>
      have hsx : 0 ≤ signed a X := by
        rcases toRat_nonneg_iff.mp hx with h | h
        · simp [h, signed]
        · subst h; cases a <;> simp [signed]
      exact sub_toRat_nonneg hsx (signed_le_of_toRat_le hle)
    | nan => simp [sub, add, neg, toRatD, toRat]
    | inf c => simp [sub, add, neg, toRatD, toRat]
  | nan => simp [sub, add, toRatD, toRat]
  | inf a =>
    cases y with
    | nan => rw [show ((inf a).sub nan).toRatD = 0 from rfl]
    | fin b Y => rw [show ((inf a).sub (fin b Y)).toRatD = 0 from rfl]
    | inf b =>
      by_cases h : a = !b
      · rw [h, show ((inf !b).sub (inf b)).toRatD = 0 from by simp only [sub, add, neg]; rfl]
      · rw [show ((inf a).sub (inf b)).toRatD = 0 from by
            simp only [sub, add, neg]; rw [ite_eq_right h]; rfl]

theorem isInt'_toRatD {s : Bool} {n : Nat} (h : (fin s n).isInt' = true) :
    ∃ k : Int, (fin s n).toRatD = k := by
  simp only [isInt'] at h
  have hm : n % unit = 0 := of_decide_eq_true h
  have hdiv : unit * (n / unit) = n := by
    have h := Nat.div_add_mod n unit
    rwa [hm, Nat.add_zero] at h
  rw [toRat_fin]
  refine ⟨signed s (n / unit), ?_⟩
  have hsn : signed s n = (unit : Int) * signed s (n / unit) := by
    cases s
    · simp only [signed_false]
      conv => lhs; rw [← hdiv]
      rw [Nat.cast_mul]
    · simp only [signed_true]
      conv => lhs; rw [← hdiv]
      rw [Nat.cast_mul, mul_neg]
  rw [hsn, Int.cast_mul]
  have c : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  rw [div_eq_iff (ne_of_gt c)]
  exact mul_comm _ _
example : (nan : F64).toRatD = 0 := rfl
example : (0:Rat) ≤ (nan : F64).toRatD := by decide

theorem jsround_toRat_nonneg' {x : F64} (hx : 0 ≤ x.toRatD) : 0 ≤ x.jsround.toRatD := by
  cases x with
  | fin s n => exact jsround_toRat_nonneg (toRat_nonneg_iff.mp hx)
  | nan => simp [jsround, toRatD, toRat]
  | inf s => simp [jsround, toRatD, toRat]

theorem rem_toRat_nonneg {x y : F64} (hx : 0 ≤ x.toRatD) :
    0 ≤ (x.rem y).toRatD := by
  cases x with
  | fin a X =>
    cases y with
    | fin b Y =>
      by_cases hY : Y = 0
      · rw [show (fin a X).rem (fin b Y) = nan from by simp [rem, hY]]
        rw [show (nan : F64).toRatD = 0 from rfl]
      · rw [show (fin a X).rem (fin b Y) = fin a (X % Y) from by simp [rem, hY],
          toRat_nonneg_iff]
        rcases toRat_nonneg_iff.mp hx with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [h]; simp)
    | nan => rw [show ((fin a X).rem nan).toRatD = 0 from rfl]
    | inf c => rw [show (fin a X).rem (inf c) = fin a X from rfl]; exact hx
  | nan => cases y with
    | nan => rw [show (nan.rem nan).toRatD = 0 from rfl]
    | inf c => rw [show (nan.rem (inf c)).toRatD = 0 from rfl]
    | fin c N => rw [show (nan.rem (fin c N)).toRatD = 0 from rfl]
  | inf a => cases y with
    | nan => rw [show ((inf a).rem nan).toRatD = 0 from rfl]
    | inf c => rw [show ((inf a).rem (inf c)).toRatD = 0 from rfl]
    | fin c N => rw [show ((inf a).rem (fin c N)).toRatD = 0 from rfl]

theorem rem_toRat_le {x y : F64} (hx : 0 ≤ x.toRatD) :
    (x.rem y).toRatD ≤ x.toRatD := by
  cases x with
  | fin a X =>
    cases y with
    | fin b Y =>
      by_cases hY : Y = 0
      · rw [show (fin a X).rem (fin b Y) = nan from by simp [rem, hY],
            show (nan : F64).toRatD = 0 from rfl]
        exact hx
      · rw [show (fin a X).rem (fin b Y) = fin a (X % Y) from by simp [rem, hY],
            toRat_fin, toRat_fin]
        rcases toRat_nonneg_iff.mp hx with h | h
        · rw [h]
          simp only [signed_false]
          gcongr
          exact Nat.mod_le X Y
        · subst h; simp
    | nan => rw [show ((fin a X).rem nan).toRatD = 0 from rfl]; exact hx
    | inf c => rw [show (fin a X).rem (inf c) = fin a X from rfl]
  | nan => cases y with
    | nan => rw [show (nan.rem nan).toRatD = 0 from rfl]; exact hx
    | inf c => rw [show (nan.rem (inf c)).toRatD = 0 from rfl]; exact hx
    | fin c N => rw [show (nan.rem (fin c N)).toRatD = 0 from rfl]; exact hx
  | inf a => cases y <;> simp [rem, toRatD, toRat]

/-- `toRatD (fin a X) ≥ 1` forces `X ≥ unit` and `a = false`; used to feed
`div_fin`'s denominator side-condition from a `toRat ≥ 1` contract hypothesis. -/
theorem unit_le_mag_of_one_le_toRatD {a : Bool} {X : Nat}
    (h : 1 ≤ (fin a X).toRatD) : unit ≤ X := by
  rw [toRat_fin] at h
  have hu : ((0 : Int) : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  have hs : ((signed a X : Int) : Rat) ≥ ((unit : Int) : Rat) := by
    have := (le_div_iff₀ hu).mp h
    simpa using this
  have hsI : (unit : Int) ≤ signed a X := Int.cast_le.mp hs
  have hup : (0 : Int) < (unit : Int) := Nat.cast_pos.mpr unit_pos
  cases a
  · simp [signed] at hsI
    omega
  · simp [signed] at hsI
    omega

/-- Magnitude comparison from value comparison: if a non-negative finite `x`'s
value is at most a non-negative finite `y`'s value, `x`'s magnitude is at most
`y`'s. The premise is stated via `toRatD` so contracts can reason about bounds
without unfolding bits. -/
theorem mag_le_of_toRatD_le {a : Bool} {X Y : Nat}
    (h0 : 0 ≤ (fin a X).toRatD) (h : (fin a X).toRatD ≤ (fin false Y).toRatD) :
    X ≤ Y := by
  rw [toRat_fin] at h0 h
  rw [toRat_fin] at h
  have hu : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  have h' : (signed a X : Rat) ≤ (signed false Y : Rat) := by
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hu)
    rw [div_mul_cancel₀ _ (ne_of_gt hu), div_mul_cancel₀ _ (ne_of_gt hu)] at h2
    exact h2
  cases a with
  | false =>
    have h3 : (X : Rat) ≤ (Y : Rat) := by simpa [signed] using h'
    exact_mod_cast h3
  | true =>
    have h0' : (0 : Rat) ≤ -((X : Nat) : Rat) / ((unit : Int) : Rat) := by
      simpa [signed] using h0
    have h2 := mul_le_mul_of_nonneg_right h0' (le_of_lt hu)
    rw [zero_mul, div_mul_cancel₀ _ (ne_of_gt hu)] at h2
    have h3 : (X : Rat) ≤ 0 := neg_nonneg.mp h2
    have : X ≤ 0 := by exact_mod_cast h3
    omega

theorem round_fin {neg : Bool} {n e : Nat} {st : Bool} {B : Nat}
    (h : n ≤ B * 2 ^ e) (hB : 2 * B + 1 < limit) :
    ∃ m, round neg n e st = fin neg m ∧ m ≤ 2 * B + 1 := by
  unfold round
  by_cases hn0 : n = 0
  · subst hn0; simp only [ite_true]; exact ⟨0, rfl, by omega⟩
  · rw [ite_eq_right hn0]
    generalize hs : max (Nat.log2 n + 1 - 53) e = s
    by_cases hs0 : s = 0
    · rw [ite_eq_left hs0]
      have he0 : e = 0 := by omega
      subst he0
      rw [Nat.pow_zero, Nat.mul_one] at h
      have hlt : ¬ limit ≤ n := by omega
      rw [ite_eq_right hlt]
      exact ⟨n, rfl, by omega⟩
    · rw [ite_eq_right hs0]
      simp only
      have hse : e ≤ s := by omega
      have hmag : n / 2 ^ s * 2 ^ (s - e) + 2 ^ (s - e) ≤ 2 * B + 1 := by
        have h1 : n / 2 ^ s * 2 ^ (s - e) ≤ n / 2 ^ e := by
          have he : 2 ^ s = 2 ^ e * 2 ^ (s - e) := by rw [← Nat.pow_add]; congr 1; omega
          rw [he, ← Nat.div_div_eq_div_mul]
          exact Nat.div_mul_le_self _ _
        have h2se : 2 ^ (s - e) ≤ n / 2 ^ e + 1 := by
          rcases Nat.eq_or_lt_of_le hse with hseq | hsgt
          · rw [← hseq]; simp
          · have hsle : s - e ≤ Nat.log2 n + 1 - 53 - e := by omega
            have hlog : 2 ^ (Nat.log2 n + 1) ≤ 2 * n := by
              rw [Nat.pow_succ]
              simpa [Nat.mul_comm] using Nat.mul_le_mul_right 2 (Nat.log2_self_le hn0)
            have hdvd : 2 ^ (s - e) * 2 ^ (53 + e) ≤ 2 * n := by
              calc 2 ^ (s - e) * 2 ^ (53 + e)
                  ≤ 2 ^ (Nat.log2 n + 1 - 53 - e) * 2 ^ (53 + e) :=
                    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hsle)
                _ = 2 ^ (Nat.log2 n + 1 - 53 - e + (53 + e)) := by rw [← Nat.pow_add]
                _ ≤ 2 ^ (Nat.log2 n + 1) := Nat.pow_le_pow_right (by decide) (by omega)
                _ ≤ 2 * n := hlog
            have hx : 2 ^ (s - e) ≤ 2 * n / 2 ^ (53 + e) :=
              (Nat.le_div_iff_mul_le (Nat.two_pow_pos (53 + e))).mpr hdvd
            have he2 : (2 : Nat) ^ (53 + e) = 2 ^ 53 * 2 ^ e := Nat.pow_add ..
            rw [he2, ← Nat.div_div_eq_div_mul] at hx
            have h2n : 2 * n / 2 ^ 53 ≤ n := by
              calc 2 * n / 2 ^ 53 ≤ 2 * n / 2 :=
                  Nat.div_le_div_left (by decide : (2:Nat) ≤ 2 ^ 53) (by decide : 0 < 2)
                _ = n := Nat.mul_div_cancel_left _ (by decide)
            exact le_trans hx (le_trans (Nat.div_le_div_right h2n) (by omega))
        have h2 : n / 2 ^ e ≤ B := Nat.div_le_of_le_mul (Nat.mul_comm B _ ▸ h)
        omega
      generalize hup : (decide (2 ^ (s - 1) < n % 2 ^ s) ||
          decide (n % 2 ^ s = 2 ^ (s - 1)) && (st || decide (n / 2 ^ s % 2 = 1))) = up
      cases up
      · rw [ite_eq_right (show ¬(false = true) from fun h => Bool.noConfusion h)]
        have hr : n / 2 ^ s * 2 ^ (s - e) ≤ 2 * B + 1 := le_trans (Nat.le_add_right _ _) hmag
        rw [ite_eq_right (Nat.not_le.mpr (lt_of_le_of_lt hr hB))]
        exact ⟨_, rfl, hr⟩
      · rw [ite_eq_left rfl]
        have hr : (n / 2 ^ s + 1) * 2 ^ (s - e) ≤ 2 * B + 1 := by
          rw [Nat.add_one_mul]; exact hmag
        rw [ite_eq_right (Nat.not_le.mpr (lt_of_le_of_lt hr hB))]
        exact ⟨_, rfl, hr⟩

/-- `add` of two finite operands is finite whenever twice the sum of their
magnitudes stays below `limit`, and the result's magnitude is bounded too. -/
theorem add_fin {a b : Bool} {X Y B : Nat} (h : X + Y ≤ B) (hB : 2 * B + 1 < limit) :
    ∃ s m, (fin a X).add (fin b Y) = fin s m ∧ m ≤ 2 * B + 1 := by
  simp only [add]
  by_cases hr0 : signed a X + signed b Y = 0
  · rw [ite_eq_left hr0]
    exact ⟨a && b, 0, rfl, by omega⟩
  · rw [ite_eq_right hr0]
    have hn : (signed a X + signed b Y).natAbs ≤ B := by
      cases a <;> cases b <;> simp [signed] at hr0 ⊢ <;> omega
    obtain ⟨m, hm, hmb⟩ := round_fin (neg := decide (signed a X + signed b Y < 0))
      (n := (signed a X + signed b Y).natAbs) (e := 0) (st := false) (B := B)
      (by simpa using hn) hB
    rw [hm]
    exact ⟨decide (signed a X + signed b Y < 0), m, rfl, hmb⟩

/-- `sub` shares `add`'s bound: `x - y` adds `x` and `-y`. -/
theorem sub_fin {a b : Bool} {X Y B : Nat} (h : X + Y ≤ B) (hB : 2 * B + 1 < limit) :
    ∃ s m, (fin a X).sub (fin b Y) = fin s m ∧ m ≤ 2 * B + 1 := by
  simp only [sub, neg]
  exact add_fin h hB

/-- `mul` of finite operands is finite under the same kind of bound. -/
theorem mul_fin {a b : Bool} {X Y B : Nat} (h : X * Y ≤ B * unit)
    (hB : 2 * B + 1 < limit) :
    ∃ m, (fin a X).mul (fin b Y) = fin (a != b) m ∧ m ≤ 2 * B + 1 := by
  simp only [mul]
  exact round_fin (h := h) hB

/-- `x / y` is finite when `y ≥ 1` (magnitude `unit`) and `x`'s magnitude is
bounded; the quotient's magnitude is bounded by `2·B·unit + 1`. -/
theorem div_fin {a b : Bool} {X Y B : Nat} (hY : unit ≤ Y) (h : X ≤ B * unit)
    (hB : 2 * (B * unit) + 1 < limit) :
    ∃ m, (fin a X).div (fin b Y) = fin (a != b) m ∧ m ≤ 2 * (B * unit) + 1 := by
  have hY0 : Y ≠ 0 := by have := unit_pos; omega
  simp only [div]
  rw [ite_eq_right hY0]
  by_cases hX0 : X = 0
  · rw [ite_eq_left hX0]
    exact ⟨0, rfl, by omega⟩
  · rw [ite_eq_right hX0]
    generalize hk : Nat.log2 Y + 64 = k
    have hn : X * 2 ^ (1074 + k) / Y ≤ (B * unit) * 2 ^ k := by
      have he : X * 2 ^ (1074 + k) = X * 2 ^ k * unit := by
        rw [Nat.pow_add, show (2:Nat) ^ 1074 = unit from rfl]; ring
      calc X * 2 ^ (1074 + k) / Y
          ≤ X * 2 ^ (1074 + k) / unit := Nat.div_le_div_left hY unit_pos
        _ = X * 2 ^ k := by rw [he, Nat.mul_div_cancel _ unit_pos]
        _ ≤ (B * unit) * 2 ^ k := Nat.mul_le_mul_right _ h
    obtain ⟨m, hm, hmb⟩ := round_fin (neg := a != b)
      (n := X * 2 ^ (1074 + k) / Y) (e := k) (st := decide (X * 2 ^ (1074 + k) % Y ≠ 0))
      (B := B * unit) hn hB
    rw [hm]
    exact ⟨m, rfl, hmb⟩

/-- `%` on a finite dividend and non-zero finite divisor is finite and no
larger than the dividend. -/
theorem rem_fin {a b : Bool} {X Y : Nat} (hY : Y ≠ 0) :
    ∃ m, (fin a X).rem (fin b Y) = fin a m ∧ m ≤ X := by
  simp only [rem]
  rw [ite_eq_right hY]
  exact ⟨X % Y, rfl, Nat.mod_le X Y⟩

/-- A magnitude bound gives a value bound. -/
theorem toRatD_le {s : Bool} {n B : Nat} (h : n ≤ B * unit) :
    (fin s n).toRatD ≤ B := by
  rw [toRat_fin]
  have hu : (0 : Rat) < ((unit : Int) : Rat) :=
    Int.cast_pos.mpr (Nat.cast_pos.mpr unit_pos)
  cases s
  · simp only [signed_false]
    rw [div_le_iff₀ hu]
    calc ((n : Int) : Rat) ≤ ((B * unit : Nat) : Rat) := by exact_mod_cast h
      _ = (B : Rat) * ((unit : Int) : Rat) := by norm_num
  · simp only [signed_true]
    apply le_trans _ (Nat.cast_nonneg (α := Rat) B)
    rw [Int.cast_neg, neg_div]
    apply neg_nonpos.mpr
    apply div_nonneg _ (le_of_lt hu)
    exact Int.cast_nonneg (Int.natCast_nonneg _)
