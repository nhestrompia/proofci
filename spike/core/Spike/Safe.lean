import F64
import Aeneas

set_option exponentiation.threshold 3000

/-! Safe integers inside binary64: the lemmas that keep today's typed view valid once
numbers are real doubles. -/
namespace Core.F64

theorem unit_pos : 0 < unit := Nat.pow_pos (by decide)

theorem signed_ofInt (a : Int) : signed (decide (a < 0)) (a.natAbs * unit) = a * (unit : Int) := by
  unfold signed
  by_cases h : a < 0
  · simp only [h, decide_true, if_true]
    push_cast
    rw [abs_of_neg h, Int.neg_mul, Int.neg_neg]
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    push_cast
    rw [abs_of_nonneg (by omega)]

theorem unit_int_pos : (0 : Int) < (unit : Int) := by exact_mod_cast unit_pos

@[simp] theorem lt_ofInt (a b : Int) : (ofInt a).lt (ofInt b) = decide (a < b) := by
  simp only [ofInt, lt, signed_ofInt]
  simp [Int.mul_lt_mul_right unit_int_pos]

@[simp] theorem eq_ofInt (a b : Int) : (ofInt a).eq (ofInt b) = decide (a = b) := by
  simp only [ofInt, eq, le.eq', signed_ofInt]
  have : (unit : Int) ≠ 0 := Int.ne_of_gt unit_int_pos
  simp [Int.mul_eq_mul_right_iff this]

@[simp] theorem le_ofInt (a b : Int) : (ofInt a).le (ofInt b) = decide (a ≤ b) := by
  have h : (ofInt a).le (ofInt b) = ((ofInt a).lt (ofInt b) || (ofInt a).eq (ofInt b)) := rfl
  rw [h, lt_ofInt, eq_ofInt]
  by_cases hab : a ≤ b
  · have : a < b ∨ a = b := by omega
    rcases this with h | h <;> simp [h]; omega
  · have h1 : ¬ a < b := by omega
    have h2 : ¬ a = b := by omega
    simp [h1, h2, hab]

/-- A safe integer in units of 2⁻¹⁰⁷⁴ is already representable, so rounding keeps it. -/
theorem round_exact {neg : Bool} {m : Nat} (h0 : 0 < m) (hm : m < 2 ^ 53) :
    round neg (m * unit) 0 false = fin neg (m * unit) := by
  have hu : unit = 2 ^ 1074 := rfl
  have hn : m * unit ≠ 0 := Nat.mul_ne_zero (by omega) (by rw [hu]; positivity)
  have hlt : m * unit < 2 ^ 1127 := by
    calc m * unit < 2 ^ 53 * unit := Nat.mul_lt_mul_of_pos_right hm unit_pos
      _ = 2 ^ 1127 := by rw [hu, ← Nat.pow_add]
  have hlog : Nat.log2 (m * unit) < 1127 := (Nat.log2_lt hn).mpr hlt
  have hlimit : ¬ limit ≤ m * unit := by
    have : (2 : Nat) ^ 1127 ≤ limit := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  unfold round
  rw [if_neg hn]
  simp only
  generalize hs : max (Nat.log2 (m * unit) + 1 - 53) 0 = s
  have hs' : s ≤ 1074 := by omega
  by_cases hs0 : s = 0
  · simp [hs0, hlimit]
  · have hdvd : 2 ^ s ∣ m * unit := by
      rw [hu]
      exact Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 hs') m
    have hrest : (m * unit) % 2 ^ s = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hhalf : 0 < 2 ^ (s - 1) := by positivity
    have hback : (m * unit) / 2 ^ s * 2 ^ s = m * unit := Nat.div_mul_cancel hdvd
    simp [hs0, hrest, Nat.ne_of_gt hhalf, hback, hlimit]

@[simp] theorem add_ofInt {a b : Int} (hlo : -9007199254740991 ≤ a + b) (hhi : a + b ≤ 9007199254740991) :
    (ofInt a).add (ofInt b) = ofInt (a + b) := by
  simp only [ofInt, add, signed_ofInt]
  have hsum : a * (unit : Int) + b * unit = (a + b) * unit := by rw [Int.add_mul]
  rw [hsum]
  have hu : (unit : Int) ≠ 0 := Int.ne_of_gt unit_int_pos
  by_cases h : a + b = 0
  · have hz : (a + b) * (unit : Int) = 0 := by rw [h, Int.zero_mul]
    rw [if_pos hz, h]
    have hnot : (decide (a < 0) && decide (b < 0)) = false := by
      by_cases ha : a < 0
      · have : ¬ b < 0 := by omega
        simp [this]
      · simp [ha]
    simp [hnot]
  · have hne : (a + b) * (unit : Int) ≠ 0 := Int.mul_ne_zero h hu
    rw [if_neg hne]
    have habs : ((a + b) * (unit : Int)).natAbs = (a + b).natAbs * unit := by
      rw [Int.natAbs_mul]; simp
    have hsign : decide ((a + b) * (unit : Int) < 0) = decide (a + b < 0) := by
      have : (a + b) * (unit : Int) < 0 ↔ a + b < 0 := by
        constructor
        · intro hx
          by_contra hc
          have : 0 ≤ (a + b) * (unit : Int) := Int.mul_nonneg (by omega) (Int.le_of_lt unit_int_pos)
          omega
        · intro hx
          exact Int.mul_neg_of_neg_of_pos hx unit_int_pos
      simp [this]
    rw [habs, hsign]
    exact round_exact (by omega) (by omega)

theorem neg_ofInt_nonzero {b : Int} (hb : b ≠ 0) : (ofInt b).neg = ofInt (-b) := by
  simp only [ofInt, neg]
  by_cases h : b < 0
  · have : ¬ -b < 0 := by omega
    simp [h, this]; omega
  · have : -b < 0 := by omega
    simp [h, this]; omega

@[simp] theorem sub_ofInt {a b : Int} (hlo : -9007199254740991 ≤ a - b) (hhi : a - b ≤ 9007199254740991) :
    (ofInt a).sub (ofInt b) = ofInt (a - b) := by
  unfold sub
  by_cases hb : b = 0
  · subst hb
    -- `x - 0` adds `-0`, which changes nothing.
    have hneg : (ofInt 0).neg = fin true 0 := by simp [ofInt, neg]
    rw [hneg]
    simp only [ofInt, add, signed_ofInt]
    by_cases ha : a = 0
    · subst ha; simp [signed]
    · have h1 : signed true 0 = 0 := by simp [signed]
      have hne : a * (unit : Int) ≠ 0 := Int.mul_ne_zero ha (Int.ne_of_gt unit_int_pos)
      simp only [h1, Int.add_zero]
      rw [if_neg hne]
      have habs : (a * (unit : Int)).natAbs = a.natAbs * unit := by rw [Int.natAbs_mul]; simp
      have hsign : decide (a * (unit : Int) < 0) = decide (a < 0) := by
        have : a * (unit : Int) < 0 ↔ a < 0 := by
          constructor
          · intro hx
            by_contra hc
            have : 0 ≤ a * (unit : Int) := Int.mul_nonneg (by omega) (Int.le_of_lt unit_int_pos)
            omega
          · intro hx
            exact Int.mul_neg_of_neg_of_pos hx unit_int_pos
        simp [this]
      rw [habs, hsign, round_exact (by omega) (by omega), Int.sub_zero]
  · rw [neg_ofInt_nonzero hb, add_ofInt (by omega) (by omega)]
    rfl

@[simp] theorem index_ofInt_nonneg {a : Int} (h : 0 ≤ a) : (ofInt a).index = some a.toNat := by
  have hneg : decide (a < 0) = false := by simp; omega
  have hmod : (a.natAbs * unit) % unit = 0 := Nat.mul_mod_left _ _
  have hdiv : (a.natAbs * unit) / unit = a.natAbs := Nat.mul_div_cancel _ unit_pos
  have hto : a.toNat = a.natAbs := by omega
  simp only [ofInt, index, hneg]
  by_cases ha : a.natAbs = 0
  · have : a = 0 := by omega
    subst this; simp
  · have : a.natAbs * unit ≠ 0 := Nat.mul_ne_zero ha (Nat.ne_of_gt unit_pos)
    simp [this, hmod, hdiv, hto]

end Core.F64
