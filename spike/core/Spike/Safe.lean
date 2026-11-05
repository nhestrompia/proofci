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

namespace Core.F64

/-- A number that stands for integer `a`. `-0` stands for 0, which is how the typed view
reads it: `===`, ordering and indexing can't tell them apart. -/
def IsInt (x : F64) (a : Int) : Prop := x = ofInt a ∨ (a = 0 ∧ x = fin true 0)

theorem round_zero (neg extra sticky) : round neg 0 extra sticky = fin neg 0 := by
  simp [round]

/-- A product of two units has every low bit clear, so rounding keeps a safe integer. -/
theorem round_mul_exact {neg : Bool} {m : Nat} (h0 : 0 < m) (hm : m < 2 ^ 53) :
    round neg (m * unit * unit) 1074 false = fin neg (m * unit) := by
  have hu : unit = 2 ^ 1074 := rfl
  have huu : unit * unit = 2 ^ 2148 := by rw [hu, ← Nat.pow_add]
  have hn : m * unit * unit = m * 2 ^ 2148 := by rw [Nat.mul_assoc, huu]
  have hne : m * 2 ^ 2148 ≠ 0 := Nat.mul_ne_zero (by omega) (by positivity)
  have hlt : m * 2 ^ 2148 < 2 ^ 2201 := by
    calc m * 2 ^ 2148 < 2 ^ 53 * 2 ^ 2148 := Nat.mul_lt_mul_of_pos_right hm (by positivity)
      _ = 2 ^ 2201 := by rw [← Nat.pow_add]
  have hlog : Nat.log2 (m * 2 ^ 2148) < 2201 := (Nat.log2_lt hne).mpr hlt
  have hlimit : ¬ limit ≤ m * unit := by
    have h1 : m * unit < 2 ^ 1127 := by
      calc m * unit < 2 ^ 53 * unit := Nat.mul_lt_mul_of_pos_right hm unit_pos
        _ = 2 ^ 1127 := by rw [hu, ← Nat.pow_add]
    have h2 : (2 : Nat) ^ 1127 ≤ limit := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  rw [hn]
  unfold round
  rw [if_neg hne]
  simp only
  generalize hs : max (Nat.log2 (m * 2 ^ 2148) + 1 - 53) 1074 = s
  have hs1 : 1074 ≤ s := by omega
  have hs2 : s ≤ 2148 := by omega
  have hs0 : s ≠ 0 := by omega
  have hdvd : 2 ^ s ∣ m * 2 ^ 2148 := Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 hs2) m
  have hrest : (m * 2 ^ 2148) % 2 ^ s = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hhalf : 0 < 2 ^ (s - 1) := by positivity
  have hback : (m * 2 ^ 2148) / 2 ^ s * 2 ^ (s - 1074) = m * unit := by
    have he : 2148 - s + s = 2148 := by omega
    have hsplit : (2 : Nat) ^ 2148 = 2 ^ (2148 - s) * 2 ^ s := by rw [← Nat.pow_add, he]
    have hdiv : (m * 2 ^ 2148) / 2 ^ s = m * 2 ^ (2148 - s) := by
      rw [hsplit, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by positivity)]
    have he : 2148 - s + (s - 1074) = 1074 := by omega
    rw [hdiv, Nat.mul_assoc, ← Nat.pow_add, he, hu]
  have h1 : decide (2 ^ (s - 1) < 0) = false := by simp
  have h2 : decide (0 = 2 ^ (s - 1)) = false := by simp
  rw [if_neg hs0]
  simp only [hrest, h1, h2, Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false, hback, if_neg hlimit]

theorem mul_isInt {a b : Int} (hlo : -9007199254740991 ≤ a * b) (hhi : a * b ≤ 9007199254740991) :
    IsInt ((ofInt a).mul (ofInt b)) (a * b) := by
  simp only [ofInt, mul]
  by_cases hab : a * b = 0
  · have hz : a.natAbs * unit * (b.natAbs * unit) = 0 := by
      have : a.natAbs * b.natAbs = 0 := by rw [← Int.natAbs_mul, hab]; rfl
      calc a.natAbs * unit * (b.natAbs * unit) = (a.natAbs * b.natAbs) * (unit * unit) := by ring
        _ = 0 := by rw [this, Nat.zero_mul]
    rw [hz, round_zero]
    cases hs : (decide (a < 0) != decide (b < 0))
    · exact Or.inl (by simp [ofInt, hab])
    · exact Or.inr ⟨hab, rfl⟩
  · have hm : a.natAbs * unit * (b.natAbs * unit) = (a * b).natAbs * unit * unit := by
      rw [Int.natAbs_mul]; ring
    rw [hm, round_mul_exact (by have := Int.natAbs_pos.mpr hab; omega) (by omega)]
    left
    have hsign : (decide (a < 0) != decide (b < 0)) = decide (a * b < 0) := by
      have ha : a ≠ 0 := fun h => hab (by simp [h])
      have hb : b ≠ 0 := fun h => hab (by simp [h])
      by_cases h1 : a < 0 <;> by_cases h2 : b < 0
      · have : 0 < a * b := mul_pos_of_neg_of_neg h1 h2
        simp [h1, h2]; omega
      · have : a * b < 0 := mul_neg_of_neg_of_pos h1 (by omega)
        simp [h1, h2, this]
      · have : a * b < 0 := mul_neg_of_pos_of_neg (by omega) h2
        simp [h1, h2, this]
      · have : 0 < a * b := mul_pos (by omega) (by omega)
        simp [h1, h2]; omega
    simp [ofInt, hsign]

/-- `-0` is invisible to ordering and `===`, so comparisons survive `IsInt`. -/
theorem lt_isInt {x y : F64} {a b : Int} (hx : IsInt x a) (hy : IsInt y b) : x.lt y = decide (a < b) := by
  rcases hx with rfl | ⟨rfl, rfl⟩ <;> rcases hy with rfl | ⟨rfl, rfl⟩
  · exact lt_ofInt a b
  · simpa [ofInt, lt, signed_ofInt, signed] using lt_ofInt a 0
  · simpa [ofInt, lt, signed_ofInt, signed] using lt_ofInt 0 b
  · simp [lt, signed]

theorem eq_isInt {x y : F64} {a b : Int} (hx : IsInt x a) (hy : IsInt y b) : x.eq y = decide (a = b) := by
  rcases hx with rfl | ⟨rfl, rfl⟩ <;> rcases hy with rfl | ⟨rfl, rfl⟩
  · exact eq_ofInt a b
  · simpa [ofInt, eq, le.eq', signed_ofInt, signed] using eq_ofInt a 0
  · simpa [ofInt, eq, le.eq', signed_ofInt, signed] using eq_ofInt 0 b
  · simp [eq, le.eq', signed]

theorem add_isInt {x y : F64} {a b : Int} (hx : IsInt x a) (hy : IsInt y b)
    (hlo : -9007199254740991 ≤ a + b) (hhi : a + b ≤ 9007199254740991) : IsInt (x.add y) (a + b) := by
  rcases hx with rfl | ⟨rfl, rfl⟩ <;> rcases hy with rfl | ⟨rfl, rfl⟩
  · exact Or.inl (add_ofInt hlo hhi)
  · -- `x - 0` is defined as `x + (-0)`, so this case is `sub_ofInt`.
    have h := sub_ofInt (a := a) (b := 0) (by omega) (by omega)
    have hneg : (ofInt 0).neg = fin true 0 := by simp [ofInt, neg]
    unfold sub at h
    rw [hneg] at h
    exact Or.inl (by simpa using h)
  · have h := sub_ofInt (a := b) (b := 0) (by omega) (by omega)
    have hneg : (ofInt 0).neg = fin true 0 := by simp [ofInt, neg]
    unfold sub at h
    rw [hneg] at h
    have hc : (fin true 0).add (ofInt b) = (ofInt b).add (fin true 0) := by
      simp only [ofInt, add, Int.add_comm, Bool.and_comm]
    exact Or.inl (by rw [hc]; simpa using h)
  · exact Or.inr ⟨by omega, by simp [add, signed]⟩

end Core.F64
