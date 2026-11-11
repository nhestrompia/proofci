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

/-- An exact quotient has every low bit clear, so rounding keeps a safe integer. -/
theorem round_div_exact {neg : Bool} {m k : Nat} (h0 : 0 < m) (hm : m < 2 ^ 53) (hk : 64 ≤ k) :
    round neg (m * 2 ^ (1074 + k)) k false = fin neg (m * unit) := by
  have hu : unit = 2 ^ 1074 := rfl
  have hne : m * 2 ^ (1074 + k) ≠ 0 := Nat.mul_ne_zero (by omega) (by positivity)
  have hlt : m * 2 ^ (1074 + k) < 2 ^ (1127 + k) := by
    calc m * 2 ^ (1074 + k) < 2 ^ 53 * 2 ^ (1074 + k) := Nat.mul_lt_mul_of_pos_right hm (by positivity)
      _ = 2 ^ (1127 + k) := by rw [← Nat.pow_add]; congr 1; omega
  have hlog : Nat.log2 (m * 2 ^ (1074 + k)) < 1127 + k := (Nat.log2_lt hne).mpr hlt
  have hlimit : ¬ limit ≤ m * unit := by
    have h1 : m * unit < 2 ^ 1127 := by
      calc m * unit < 2 ^ 53 * unit := Nat.mul_lt_mul_of_pos_right hm unit_pos
        _ = 2 ^ 1127 := by rw [hu, ← Nat.pow_add]
    have h2 : (2 : Nat) ^ 1127 ≤ limit := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  unfold round
  rw [if_neg hne]
  simp only
  generalize hs : max (Nat.log2 (m * 2 ^ (1074 + k)) + 1 - 53) k = s
  have hs1 : k ≤ s := by omega
  have hs2 : s ≤ 1074 + k := by omega
  have hs0 : s ≠ 0 := by omega
  have hdvd : 2 ^ s ∣ m * 2 ^ (1074 + k) := Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 hs2) m
  have hrest : (m * 2 ^ (1074 + k)) % 2 ^ s = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hback : (m * 2 ^ (1074 + k)) / 2 ^ s * 2 ^ (s - k) = m * unit := by
    have he : 1074 + k - s + s = 1074 + k := by omega
    have hsplit : (2 : Nat) ^ (1074 + k) = 2 ^ (1074 + k - s) * 2 ^ s := by rw [← Nat.pow_add, he]
    have hdiv : (m * 2 ^ (1074 + k)) / 2 ^ s = m * 2 ^ (1074 + k - s) := by
      rw [hsplit, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by positivity)]
    have he' : 1074 + k - s + (s - k) = 1074 := by omega
    rw [hdiv, Nat.mul_assoc, ← Nat.pow_add, he', hu]
  have h1 : decide (2 ^ (s - 1) < 0) = false := by simp
  have h2 : decide (0 = 2 ^ (s - 1)) = false := by simp
  rw [if_neg hs0]
  simp only [hrest, h1, h2, Bool.false_or, Bool.false_and, Bool.false_eq_true, ite_false, hback, if_neg hlimit]

theorem sign_mul {b q : Int} (hb : b ≠ 0) (hq : q ≠ 0) :
    (decide (b * q < 0) != decide (b < 0)) = decide (q < 0) := by
  by_cases h1 : b < 0 <;> by_cases h2 : q < 0
  · have : 0 < b * q := mul_pos_of_neg_of_neg h1 h2
    simp [h1, h2]; omega
  · have : b * q < 0 := mul_neg_of_neg_of_pos h1 (by omega)
    simp [h1, h2, this]
  · have : b * q < 0 := mul_neg_of_pos_of_neg (by omega) h2
    simp [h1, h2, this]
  · have : 0 < b * q := mul_pos (by omega) (by omega)
    simp [h1, h2]; omega

/-- Dividing two doubles that stand for integers, when the quotient is a safe integer. -/
theorem div_isInt {x y : F64} {b q : Int} (hx : IsInt x (b * q)) (hy : IsInt y b) (hb : b ≠ 0)
    (hlo : -9007199254740991 ≤ q) (hhi : q ≤ 9007199254740991) : IsInt (x.div y) q := by
  have hy' : y = ofInt b := by rcases hy with h | ⟨h, _⟩; exact h; exact absurd h hb
  subst hy'
  have hbn : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hyn : b.natAbs * unit ≠ 0 := Nat.mul_ne_zero (by omega) (Nat.ne_of_gt unit_pos)
  by_cases hq : q = 0
  · subst hq
    have hz : x = fin false 0 ∨ x = fin true 0 := by
      rcases hx with h | ⟨_, h⟩
      · left; rw [h]; simp [ofInt]
      · right; exact h
    have zero : ∀ s, IsInt (fin s 0) 0 := fun s => by
      cases s
      · exact Or.inl (by simp [ofInt])
      · exact Or.inr ⟨rfl, rfl⟩
    rcases hz with rfl | rfl <;> simp only [ofInt, div, if_neg hyn, if_true] <;> exact zero _
  · have hab : b * q ≠ 0 := Int.mul_ne_zero hb hq
    have hx' : x = ofInt (b * q) := by rcases hx with h | ⟨h, _⟩; exact h; exact absurd h hab
    subst hx'
    have hxn : (b * q).natAbs * unit ≠ 0 := Nat.mul_ne_zero (by have := Int.natAbs_pos.mpr hab; omega) (Nat.ne_of_gt unit_pos)
    have hqn : 0 < q.natAbs := Int.natAbs_pos.mpr hq
    generalize hk : Nat.log2 (b.natAbs * unit) + 64 = k
    have htop : (b * q).natAbs * unit * 2 ^ (1074 + k) = (b.natAbs * unit) * (q.natAbs * 2 ^ (1074 + k)) := by
      rw [Int.natAbs_mul]; ring
    simp only [ofInt, div, if_neg hyn, if_neg hxn, hk, htop]
    rw [Nat.mul_div_cancel_left _ (by omega), Nat.mul_mod_right]
    simp only [ne_eq, not_true_eq_false, decide_false]
    rw [round_div_exact hqn (by omega) (by omega), sign_mul hb hq]
    left; rfl

theorem trunc_isInt {x : F64} {a : Int} (h : IsInt x a) : IsInt x.trunc a := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · left; simp only [ofInt, trunc, Nat.mul_div_cancel _ unit_pos]
  · right; exact ⟨rfl, by simp [trunc]⟩

theorem floor_isInt {x : F64} {a : Int} (h : IsInt x a) : IsInt x.floor a := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · left
    cases hs : decide (a < 0) <;> simp [ofInt, hs, floor, trunc, Nat.mul_div_cancel _ unit_pos, Nat.mul_mod_left]
  · right; exact ⟨rfl, by simp [floor]⟩

theorem ceil_isInt {x : F64} {a : Int} (h : IsInt x a) : IsInt x.ceil a := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · left
    cases hs : decide (a < 0) with
    | false => simp [ofInt, hs, ceil, Nat.mul_mod_left]
    | true =>
      have : a.natAbs ≠ 0 := by simp at hs; omega
      simp [ofInt, hs, ceil, Nat.mul_div_cancel _ unit_pos, this]
  · right; exact ⟨rfl, by simp [ceil]⟩

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


/-! Rounding a quotient: `%`, and `Math.floor/ceil/trunc(a / b)` when `b` need not divide `a`. -/

theorem round_bounds {neg sticky : Bool} {N k s L M : Nat} (hN0 : N ≠ 0) (hs0 : s ≠ 0)
    (hs : max (N.log2 + 1 - 53) k = s) 
    (hL : L ≤ N / 2 ^ s)
    (hLeq : L = N / 2 ^ s → 2 ^ (s - 1) < N % 2 ^ s ∨ (N % 2 ^ s = 2 ^ (s - 1) ∧ sticky = true))
    (hM : N / 2 ^ s < M)
    (hMeq : N / 2 ^ s + 1 = M → N % 2 ^ s < 2 ^ (s - 1))
    (hlim : M * 2 ^ (s - k) ≤ limit) :
    ∃ R, round neg N k sticky = fin neg R ∧ L * 2 ^ (s - k) < R ∧ R < M * 2 ^ (s - k) := by
  have hks : k ≤ s := by omega
  have hW : 0 < 2 ^ (s - k) := by positivity
  unfold round
  rw [ite_eq_right_iff.mpr (fun h => absurd h hN0)]
  simp only
  rw [hs, ite_eq_right_iff.mpr (fun h => absurd h hs0)]
  generalize hm : (if (decide (2 ^ (s - 1) < N % 2 ^ s) ||
      decide (N % 2 ^ s = 2 ^ (s - 1)) && (sticky || decide (N / 2 ^ s % 2 = 1))) = true
      then N / 2 ^ s + 1 else N / 2 ^ s) = m
  have hmL : L < m := by
    rw [← hm]
    split
    · omega
    · rename_i hup
      rcases Nat.lt_or_ge L (N / 2 ^ s) with h | h
      · omega
      · have h' : L = N / 2 ^ s := by omega
        rcases hLeq h' with h1 | ⟨h1, h2⟩
        · exfalso; apply hup; simp [h1]
        · exfalso; apply hup; simp [h1, h2]
  have hmM : m < M := by
    rw [← hm]
    split
    · rename_i hup
      rcases Nat.lt_or_ge (N / 2 ^ s + 1) M with h | h
      · omega
      · have h' : N / 2 ^ s + 1 = M := by omega
        have := hMeq h'
        exfalso
        simp at hup
        rcases hup with h1 | ⟨h1, _⟩ <;> omega
    · omega
  have h1 : m * 2 ^ (s - k) < M * 2 ^ (s - k) := Nat.mul_lt_mul_of_pos_right hmM hW
  have h2 : L * 2 ^ (s - k) < m * 2 ^ (s - k) := Nat.mul_lt_mul_of_pos_right hmL hW
  refine ⟨m * 2 ^ (s - k), ?_, h2, h1⟩
  have : ¬ limit ≤ m * 2 ^ (s - k) := by omega
  rw [if_neg this]

theorem round_div_between {neg sticky : Bool} {k B n r : Nat} (hk : 64 ≤ k) (hB : 0 < B) (hBl : B < 2 ^ 53)
    (hr0 : 0 < r) (hrB : r < B) (hAl : B * n + r < 2 ^ 53)
    (hst : sticky = decide ((B * n + r) * 2 ^ (1074 + k) % B ≠ 0)) :
    ∃ R, round neg ((B * n + r) * 2 ^ (1074 + k) / B) k sticky = fin neg R ∧
      n * unit < R ∧ R < (n + 1) * unit := by
  have hunit : unit = 2 ^ 1074 := rfl
  obtain ⟨U, hU⟩ : ∃ U, U = 2 ^ (1074 + k) := ⟨_, rfl⟩
  rw [← hU] at hst ⊢
  have hU53 : 2 ^ 53 ≤ U := hU ▸ Nat.pow_le_pow_right (by omega) (by omega)
  have hBU : B < U := by omega
  obtain ⟨N, hN⟩ : ∃ N, N = (B * n + r) * U / B := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (B * n + r) * U % B := ⟨_, rfl⟩
  rw [← hρ] at hst
  have hρB : ρ < B := hρ ▸ Nat.mod_lt _ hB
  have hdm : B * N + ρ = (B * n + r) * U := by rw [hN, hρ]; exact Nat.div_add_mod _ B
  have hAU : (B * n + r) * U = B * (n * U) + r * U := by ring
  have hrU : U ≤ r * U := Nat.le_mul_of_pos_left U hr0
  have hrU2 : (r + 1) * U ≤ B * U := Nat.mul_le_mul_right U hrB
  have hrU3 : (r + 1) * U = r * U + U := by ring
  have hnUN : n * U ≤ N := by
    have : B * (n * U) < B * N := by omega
    exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left this)
  obtain ⟨q0, hq0⟩ := Nat.exists_eq_add_of_le hnUN
  have hBq : B * q0 + ρ = r * U := by
    have : B * N = B * (n * U) + B * q0 := by rw [hq0, Nat.mul_add]
    omega
  have hq0U : q0 < U := by
    have : B * q0 < B * U := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hF3 : U ≤ B * (U - q0) := by
    have h : B * (U - q0) + B * q0 = B * U := by rw [← Nat.mul_add, Nat.sub_add_cancel hq0U.le]
    omega
  have hq1 : 1 ≤ q0 := by
    rcases Nat.eq_zero_or_pos q0 with h | h
    · subst h; omega
    · exact h
  have hN0 : N ≠ 0 := by omega
  have hn1 : n + 1 ≤ 2 ^ 53 := by
    have : n ≤ B * n := Nat.le_mul_of_pos_left n hB
    omega
  have hNlt : N < 2 ^ 53 * U := by
    have h1 : (n + 1) * U ≤ 2 ^ 53 * U := Nat.mul_le_mul_right U hn1
    have h2 : (n + 1) * U = n * U + U := by ring
    omega
  obtain ⟨s, hs⟩ : ∃ s, s = max (N.log2 + 1 - 53) k := ⟨_, rfl⟩
  have hks : k ≤ s := by omega
  have hs0 : s ≠ 0 := by omega
  have hsE : s ≤ 1074 + k := by
    have h1 : N.log2 < 53 + (1074 + k) := by
      rw [Nat.log2_lt hN0, Nat.pow_add, ← hU]; exact hNlt
    omega
  -- half a unit in the last place is below the gap to the next integer
  have hH : B * 2 ^ (s - 1) < U := by
    have hs1 : s - 1 + 53 = s + 52 := by omega
    have hpow : 2 ^ (s - 1) * 2 ^ 53 = 2 ^ (s + 52) := by rw [← Nat.pow_add, hs1]
    have hP : 0 < 2 ^ 53 := by positivity
    have hHpos : 0 < 2 ^ (s - 1) := by positivity
    rcases Nat.lt_or_ge (N.log2 + 1 - 53) k with h | h
    · have hsk : s = k := by omega
      have h2 : 2 ^ (s + 52) ≤ U := by rw [hU]; exact Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : B * 2 ^ (s - 1) < 2 ^ 53 * 2 ^ (s - 1) := Nat.mul_lt_mul_of_pos_right hBl hHpos
      have h4 : 2 ^ 53 * 2 ^ (s - 1) = 2 ^ (s + 52) := by rw [Nat.mul_comm]; exact hpow
      omega
    · have hsl : s = N.log2 + 1 - 53 := by omega
      have hse : s + 52 = N.log2 := by omega
      have h2 : 2 ^ (s + 52) = 2 ^ N.log2 := by rw [hse]
      have h3 : 2 ^ N.log2 ≤ N := Nat.log2_self_le hN0
      have h4 : B * 2 ^ (s - 1) * 2 ^ 53 ≤ B * N := by
        calc B * 2 ^ (s - 1) * 2 ^ 53 = B * (2 ^ (s - 1) * 2 ^ 53) := by ring
          _ = B * 2 ^ N.log2 := by rw [hpow, h2]
          _ ≤ B * N := Nat.mul_le_mul_left B h3
      have h5 : (B * n + r) * U < 2 ^ 53 * U := Nat.mul_lt_mul_of_pos_right hAl (by omega)
      have h6 : B * 2 ^ (s - 1) * 2 ^ 53 < U * 2 ^ 53 := by
        have : U * 2 ^ 53 = 2 ^ 53 * U := Nat.mul_comm _ _
        omega
      exact Nat.lt_of_mul_lt_mul_right h6
  -- scale by units of the last place
  obtain ⟨T, hT⟩ : ∃ T, T = 2 ^ (1074 + k - s) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = 2 ^ (s - k) := ⟨_, rfl⟩
  have hD : 2 ^ s = 2 * 2 ^ (s - 1) := by
    have h1 : s = (s - 1) + 1 := by omega
    calc 2 ^ s = 2 ^ ((s - 1) + 1) := by rw [← h1]
      _ = 2 * 2 ^ (s - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hTD : T * 2 ^ s = U := by rw [hT, hU]; exact Nat.pow_sub_mul_pow 2 hsE
  have hTW : T * W = unit := by
    have h1 : 1074 + k - s + (s - k) = 1074 := by omega
    rw [hT, hW, hunit, ← Nat.pow_add, h1]
  have hWpos : 0 < W := by rw [hW]; positivity
  have hDpos : 0 < 2 ^ s := by positivity
  have hHpos : 0 < 2 ^ (s - 1) := by positivity
  have hkept : N / 2 ^ s * 2 ^ s + N % 2 ^ s = N := by rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hrest : N % 2 ^ s < 2 ^ s := Nat.mod_lt _ hDpos
  have hH' : B * 2 ^ (s - 1) < B * (U - q0) := lt_of_lt_of_le hH hF3
  have hHq : 2 ^ (s - 1) < U - q0 := Nat.lt_of_mul_lt_mul_left hH'
  have hnTD : n * T * 2 ^ s = n * U := by rw [Nat.mul_assoc, hTD]
  have hn1TD : (n + 1) * T * 2 ^ s = n * U + U := by rw [Nat.mul_assoc, hTD]; ring
  obtain ⟨R, hR, hR1, hR2⟩ := round_bounds (neg := neg) (sticky := sticky) (k := k) (L := n * T) (M := (n + 1) * T)
    hN0 hs0 hs.symm
    (by rw [Nat.le_div_iff_mul_le hDpos, hnTD]; omega)
    (by
      intro hLeq
      have hr' : N % 2 ^ s = q0 := by
        rw [← hLeq] at hkept
        omega
      rw [hr']
      rcases Nat.lt_trichotomy q0 (2 ^ (s - 1)) with h | h | h
      · exfalso
        have : B * (q0 + 1) ≤ B * 2 ^ (s - 1) := Nat.mul_le_mul_left B h
        rw [Nat.mul_add] at this
        omega
      · right
        refine ⟨h, ?_⟩
        rw [hst]
        have : ρ ≠ 0 := by
          rw [h] at hBq
          omega
        simp [this]
      · left; exact h)
    (by rw [Nat.div_lt_iff_lt_mul hDpos, hn1TD]; omega)
    (by
      intro hM
      have : N % 2 ^ s = q0 + 2 ^ s - U := by
        have hh : (n + 1) * T * 2 ^ s = (N / 2 ^ s + 1) * 2 ^ s := by rw [hM]
        have hh' : (N / 2 ^ s + 1) * 2 ^ s = N / 2 ^ s * 2 ^ s + 2 ^ s := by ring
        omega
      rw [this]
      omega)
    (by
      have h1 : (n + 1) * T * 2 ^ (s - k) = (n + 1) * unit := by rw [← hW, Nat.mul_assoc, hTW]
      rw [h1]
      calc (n + 1) * unit ≤ 2 ^ 53 * unit := Nat.mul_le_mul_right _ hn1
        _ = 2 ^ 1127 := by rw [hunit, ← Nat.pow_add]
        _ ≤ limit := Nat.pow_le_pow_right (by decide) (by decide))
  rw [← hW] at hR1 hR2
  refine ⟨R, hR, ?_, ?_⟩
  · rw [← hTW, ← Nat.mul_assoc]; exact hR1
  · rw [← hTW, ← Nat.mul_assoc]; exact hR2

theorem isInt_unit (neg : Bool) (m : Nat) : IsInt (fin neg (m * unit)) (if neg then -(m : Int) else (m : Int)) := by
  cases neg
  · left; simp [ofInt]
  · by_cases hm : m = 0
    · subst hm; right; simp
    · left; have : 0 < m := by omega
      simp [ofInt, this, Int.natAbs_neg]

/-- A quotient that is not whole rounds to a double strictly between its neighbours. -/
theorem div_between {sa sb : Bool} {A B : Nat} (hB : 0 < B) (hBl : B < 2 ^ 53) (hAl : A < 2 ^ 53)
    (hnd : A % B ≠ 0) :
    ∃ R, (fin sa (A * unit)).div (fin sb (B * unit)) = fin (sa != sb) R ∧
      (A / B) * unit < R ∧ R < (A / B + 1) * unit := by
  have hA0 : A ≠ 0 := fun h => hnd (by simp [h])
  have hyn : B * unit ≠ 0 := Nat.mul_ne_zero (by omega) (Nat.ne_of_gt unit_pos)
  have hxn : A * unit ≠ 0 := Nat.mul_ne_zero hA0 (Nat.ne_of_gt unit_pos)
  have hr0 : 0 < A % B := Nat.pos_of_ne_zero hnd
  have hrB : A % B < B := Nat.mod_lt _ hB
  have hAe : A = B * (A / B) + A % B := (Nat.div_add_mod A B).symm
  generalize hk : Nat.log2 (B * unit) + 64 = k
  have hk64 : 64 ≤ k := by omega
  have htop : A * unit * 2 ^ (1074 + k) = unit * (A * 2 ^ (1074 + k)) := by ring
  have hy : B * unit = unit * B := Nat.mul_comm _ _
  have hdiv : (fin sa (A * unit)).div (fin sb (B * unit)) =
      round (sa != sb) (A * 2 ^ (1074 + k) / B) k (decide (A * 2 ^ (1074 + k) % B ≠ 0)) := by
    simp only [div, if_neg hyn, if_neg hxn, hk]
    rw [htop, hy, Nat.mul_div_mul_left _ _ unit_pos, Nat.mul_mod_mul_left]
    have : decide (unit * (A * 2 ^ (1074 + k) % B) ≠ 0) = decide (A * 2 ^ (1074 + k) % B ≠ 0) := by
      apply decide_eq_decide.mpr
      constructor
      · intro h h0; apply h; rw [h0, Nat.mul_zero]
      · intro h h0; apply h; exact (Nat.mul_eq_zero.mp h0).resolve_left (Nat.ne_of_gt unit_pos)
    rw [this]
  rw [hdiv]
  generalize hn : A / B = n at *
  generalize hr : A % B = r at *
  subst hAe
  exact round_div_between hk64 hB hBl hr0 hrB hAl rfl


theorem fdiv_pp (A B : Nat) (hB : 0 < B) : Int.fdiv (A : Int) (B : Int) = ((A / B : Nat) : Int) := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega), Int.natCast_div]

theorem tdiv_pp (A B : Nat) : Int.tdiv (A : Int) (B : Int) = ((A / B : Nat) : Int) := by
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.natCast_div]

theorem fdiv_mag {a b : Int} (hb : b ≠ 0) (hn : ¬ b ∣ a) :
    Int.fdiv a b = if (a < 0 ↔ b < 0) then ((a.natAbs / b.natAbs : Nat) : Int)
      else -((a.natAbs / b.natAbs : Nat) : Int) - 1 := by
  have hB : 0 < b.natAbs := by omega
  have hA : 0 < a.natAbs := by
    have : a ≠ 0 := fun h => hn (by simp [h])
    omega
  have hnd : ¬ (b.natAbs : Int) ∣ (a.natAbs : Int) := by
    rcases Int.natAbs_eq a with ha | ha <;> rcases Int.natAbs_eq b with hb' | hb' <;>
      (intro h; apply hn; rw [ha, hb']; simpa [Int.neg_dvd, Int.dvd_neg] using h)
  rcases Int.natAbs_eq a with ha | ha <;> rcases Int.natAbs_eq b with hb' | hb'
  all_goals
    generalize b.natAbs = B at *
    generalize a.natAbs = A at *
    subst ha hb'
  · have h1 : ¬ ((A : Int) < 0) := by omega
    have h2 : ¬ ((B : Int) < 0) := by omega
    simp [h1, h2, fdiv_pp A B hB]
  · have h1 : ¬ ((A : Int) < 0) := by omega
    have h2 : (-(B : Int)) < 0 := by omega
    have hd : ¬ (B : Int) ∣ A := hnd
    simp only [h1, h2, iff_false, not_false_eq_true, ite_false, Int.fdiv_neg (by omega : (B : Int) ≠ 0), if_neg hd, fdiv_pp A B hB]
    simp
  · have h1 : (-(A : Int)) < 0 := by omega
    have h2 : ¬ ((B : Int) < 0) := by omega
    have hd : ¬ (B : Int) ∣ A := hnd
    simp only [h1, h2, iff_false, not_false_eq_true, ite_false, Int.neg_fdiv, fdiv_pp A B hB]
    simp [hd]
    omega
  · have h1 : (-(A : Int)) < 0 := by omega
    have h2 : (-(B : Int)) < 0 := by omega
    have hd : ¬ (B : Int) ∣ A := hnd
    simp only [h1, h2, iff_true, ite_true, Int.neg_fdiv]
    have hB0 : B ≠ 0 := by omega
    simp [Int.fdiv_neg (by omega : (B : Int) ≠ 0), hd, fdiv_pp A B hB, hB0]

/-- `Int.tdiv` read through magnitudes. -/
theorem tdiv_mag {a b : Int} (hb : b ≠ 0) :
    Int.tdiv a b = if (a < 0 ↔ b < 0) then ((a.natAbs / b.natAbs : Nat) : Int)
      else -((a.natAbs / b.natAbs : Nat) : Int) := by
  have hB : 0 < b.natAbs := by omega
  rcases Int.natAbs_eq a with ha | ha <;> rcases Int.natAbs_eq b with hb' | hb'
  all_goals
    generalize b.natAbs = B at *
    generalize a.natAbs = A at *
    subst ha hb'
  · have h2 : ¬ ((B : Int) < 0) := by omega
    simp [tdiv_pp A B, h2]
  · have h2 : (-(B : Int)) < 0 := by omega
    by_cases hA : A = 0
    · subst hA; simp
    · have h1 : ¬ ((A : Int) < 0) := by omega
      simp [Int.tdiv_neg, tdiv_pp A B, h1]
      omega
  · have h2 : ¬ ((B : Int) < 0) := by omega
    by_cases hA : A = 0
    · subst hA; simp
    · have h1 : (-(A : Int)) < 0 := by omega
      simp [Int.neg_tdiv, tdiv_pp A B, h2]
      omega
  · have h2 : (-(B : Int)) < 0 := by omega
    by_cases hA : A = 0
    · subst hA; simp
    · have h1 : (-(A : Int)) < 0 := by omega
      simp [Int.neg_tdiv, Int.tdiv_neg, tdiv_pp A B]
      omega

/-- `-Int.fdiv (-a) b` (what `Math.ceil` of a quotient is). -/
theorem cdiv_mag {a b : Int} (hb : b ≠ 0) (hn : ¬ b ∣ a) :
    -Int.fdiv (-a) b = if (a < 0 ↔ b < 0) then ((a.natAbs / b.natAbs : Nat) : Int) + 1
      else -((a.natAbs / b.natAbs : Nat) : Int) := by
  have hn' : ¬ b ∣ -a := fun h => hn (Int.dvd_neg.mp h)
  rw [fdiv_mag hb hn', Int.natAbs_neg]
  have : a ≠ 0 := fun h => hn (by simp [h])
  generalize ((a.natAbs / b.natAbs : Nat) : Int) = n
  split_ifs <;> omega


theorem rounded_cases {x y : F64} {a b : Int} (hx : IsInt x a) (hy : IsInt y b) (hb : b ≠ 0)
    (hna : ¬ b ∣ a) (ha1 : -9007199254740991 ≤ a) (ha2 : a ≤ 9007199254740991)
    (hb1 : -9007199254740991 ≤ b) (hb2 : b ≤ 9007199254740991) :
    ∃ R, x.div y = fin (decide (a < 0) != decide (b < 0)) R ∧
      (a.natAbs / b.natAbs) * unit < R ∧ R < (a.natAbs / b.natAbs + 1) * unit := by
  have ha0 : a ≠ 0 := fun h => hna (by simp [h])
  have hx' : x = ofInt a := by rcases hx with h | ⟨h, _⟩; exact h; exact absurd h ha0
  have hy' : y = ofInt b := by rcases hy with h | ⟨h, _⟩; exact h; exact absurd h hb
  subst hx' hy'
  have hnd : a.natAbs % b.natAbs ≠ 0 := fun h =>
    hna (Int.natAbs_dvd_natAbs.mp (Nat.dvd_of_mod_eq_zero h))
  simp only [ofInt]
  exact div_between (by omega) (by omega) (by omega) hnd

theorem sign_cases (a b : Int) :
    ((decide (a < 0) != decide (b < 0)) = false ∧ (a < 0 ↔ b < 0)) ∨
    ((decide (a < 0) != decide (b < 0)) = true ∧ ¬ (a < 0 ↔ b < 0)) := by
  by_cases h1 : a < 0 <;> by_cases h2 : b < 0 <;> simp [h1, h2]

theorem div_exact_val {a b q : Int} (hb : b ≠ 0) (hq : a = b * q)
    (ha1 : -9007199254740991 ≤ a) (ha2 : a ≤ 9007199254740991) :
    -9007199254740991 ≤ q ∧ q ≤ 9007199254740991 := by
  have : q.natAbs ≤ a.natAbs := by
    rw [hq, Int.natAbs_mul]
    exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hb)
  omega

theorem floorDiv_isInt {x y : F64} {a b : Int} (hx : IsInt x a) (hy : IsInt y b) (hb : b ≠ 0)
    (ha1 : -9007199254740991 ≤ a) (ha2 : a ≤ 9007199254740991)
    (hb1 : -9007199254740991 ≤ b) (hb2 : b ≤ 9007199254740991) :
    IsInt (x.div y).floor (Int.fdiv a b) := by
  by_cases hd : b ∣ a
  · obtain ⟨q, hq⟩ := hd
    have hqb := div_exact_val hb hq ha1 ha2
    have h : IsInt (x.div y) q := div_isInt (hq ▸ hx) hy hb hqb.1 hqb.2
    have hf : Int.fdiv a b = q := by
      rw [Int.fdiv_eq_ediv, hq, Int.mul_ediv_cancel_left _ hb]
      simp [Int.dvd_mul_right]
    rw [hf]; exact floor_isInt h
  · obtain ⟨R, hR, h1, h2⟩ := rounded_cases hx hy hb hd ha1 ha2 hb1 hb2
    rw [hR, fdiv_mag hb hd]
    generalize a.natAbs / b.natAbs = n at *
    have hq : R / unit = n := Nat.div_eq_of_lt_le (Nat.le_of_lt h1) h2
    have hm : R % unit ≠ 0 := by
      intro h0
      have h3 := Nat.div_add_mod R unit
      rw [hq, h0] at h3
      rw [Nat.mul_comm] at h3
      omega
    rcases sign_cases a b with ⟨hn, hs⟩ | ⟨hn, hs⟩
    · rw [hn, if_pos hs]
      simp only [floor, trunc, hq]
      exact isInt_unit false n
    · rw [hn, if_neg hs]
      simp only [floor, if_neg hm, hq]
      have := isInt_unit true (n + 1)
      simp only [if_true] at this
      push_cast at this
      have e : -(↑n : Int) - 1 = -(↑n + 1) := by omega
      rw [e]; exact this

theorem ceilDiv_isInt {x y : F64} {a b : Int} (hx : IsInt x a) (hy : IsInt y b) (hb : b ≠ 0)
    (ha1 : -9007199254740991 ≤ a) (ha2 : a ≤ 9007199254740991)
    (hb1 : -9007199254740991 ≤ b) (hb2 : b ≤ 9007199254740991) :
    IsInt (x.div y).ceil (-Int.fdiv (-a) b) := by
  by_cases hd : b ∣ a
  · obtain ⟨q, hq⟩ := hd
    have hqb := div_exact_val hb hq ha1 ha2
    have h : IsInt (x.div y) q := div_isInt (hq ▸ hx) hy hb hqb.1 hqb.2
    have hf : -Int.fdiv (-a) b = q := by
      have : -a = b * (-q) := by rw [hq]; ring
      rw [Int.fdiv_eq_ediv, this, Int.mul_ediv_cancel_left _ hb]
      simp [Int.dvd_mul_right]
    rw [hf]; exact ceil_isInt h
  · obtain ⟨R, hR, h1, h2⟩ := rounded_cases hx hy hb hd ha1 ha2 hb1 hb2
    rw [hR, cdiv_mag hb hd]
    generalize a.natAbs / b.natAbs = n at *
    have hq : R / unit = n := Nat.div_eq_of_lt_le (Nat.le_of_lt h1) h2
    have hm : R % unit ≠ 0 := by
      intro h0
      have h3 := Nat.div_add_mod R unit
      rw [hq, h0] at h3
      rw [Nat.mul_comm] at h3
      omega
    rcases sign_cases a b with ⟨hn, hs⟩ | ⟨hn, hs⟩
    · rw [hn, if_pos hs]
      simp only [ceil, if_neg hm, hq]
      have := isInt_unit false (n + 1)
      simpa using this
    · rw [hn, if_neg hs]
      simp only [ceil, hq]
      by_cases h0 : n = 0
      · subst h0
        simp only [if_true, Nat.zero_mul]
        have := isInt_unit true 0
        simpa using this
      · simp only [if_neg h0]
        exact isInt_unit true n

theorem truncDiv_isInt {x y : F64} {a b : Int} (hx : IsInt x a) (hy : IsInt y b) (hb : b ≠ 0)
    (ha1 : -9007199254740991 ≤ a) (ha2 : a ≤ 9007199254740991)
    (hb1 : -9007199254740991 ≤ b) (hb2 : b ≤ 9007199254740991) :
    IsInt (x.div y).trunc (Int.tdiv a b) := by
  by_cases hd : b ∣ a
  · obtain ⟨q, hq⟩ := hd
    have hqb := div_exact_val hb hq ha1 ha2
    have h : IsInt (x.div y) q := div_isInt (hq ▸ hx) hy hb hqb.1 hqb.2
    have hf : Int.tdiv a b = q := by
      rw [Int.tdiv_eq_ediv, hq, Int.mul_ediv_cancel_left _ hb]
      simp [Int.dvd_mul_right]
    rw [hf]; exact trunc_isInt h
  · obtain ⟨R, hR, h1, h2⟩ := rounded_cases hx hy hb hd ha1 ha2 hb1 hb2
    rw [hR, tdiv_mag hb]
    generalize a.natAbs / b.natAbs = n at *
    have hq : R / unit = n := Nat.div_eq_of_lt_le (Nat.le_of_lt h1) h2
    rcases sign_cases a b with ⟨hn, hs⟩ | ⟨hn, hs⟩
    · rw [hn, if_pos hs]
      simp only [trunc, hq]
      exact isInt_unit false n
    · rw [hn, if_neg hs]
      simp only [trunc, hq]
      have := isInt_unit true n
      simpa using this

theorem rem_isInt {x y : F64} {a b : Int} (hx : IsInt x a) (hy : IsInt y b) (hb : b ≠ 0) :
    IsInt (x.rem y) (Int.tmod a b) := by
  have hy' : y = ofInt b := by rcases hy with h | ⟨h, _⟩; exact h; exact absurd h hb
  subst hy'
  have hbn : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hyn : b.natAbs * unit ≠ 0 := Nat.mul_ne_zero (by omega) (Nat.ne_of_gt unit_pos)
  rcases hx with rfl | ⟨rfl, rfl⟩
  · simp only [ofInt, rem, if_neg hyn]
    rw [Nat.mul_mod_mul_right]
    have hnat : (Int.tmod a b).natAbs = a.natAbs % b.natAbs := Int.natAbs_tmod a b
    by_cases ha : a < 0
    · have hle : Int.tmod a b ≤ 0 := by
        have := Int.tmod_nonneg b (a := -a) (by omega)
        rw [Int.neg_tmod] at this; omega
      by_cases ht : Int.tmod a b = 0
      · right
        refine ⟨ht, ?_⟩
        have : a.natAbs % b.natAbs = 0 := by rw [← hnat, ht]; rfl
        simp [ha, this]
      · left
        have hlt : Int.tmod a b < 0 := by omega
        simp [ofInt, ha, hlt, hnat]
    · have hge : 0 ≤ Int.tmod a b := Int.tmod_nonneg b (by omega)
      left
      have hlt : ¬ Int.tmod a b < 0 := by omega
      simp [ofInt, ha, hlt, hnat]
  · have : Int.tmod 0 b = 0 := by simp
    rw [this]
    right
    refine ⟨rfl, ?_⟩
    simp [rem, ofInt, hyn]


end Core.F64
