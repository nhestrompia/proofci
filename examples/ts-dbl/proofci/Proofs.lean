import TsDbl
open Aeneas Aeneas.Std Result src.pricing

set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 2000000

/-- The two bit-literal constants the generated code uses, as `F64` values
contracts can reason about. `100` (`0x4059…`) and `1` (`0x3ff0…`). -/
private theorem hund_f :
    (Js.Dbl.lit 0x4059000000000000).f = Core.F64.fin false (100 * Core.F64.unit) := by
  decide

private theorem one_f :
    (Js.Dbl.lit 0x3ff0000000000000).f = Core.F64.fin false Core.F64.unit := by
  decide

private theorem hund_rat :
    (Core.F64.fin false (100 * Core.F64.unit)).toRatD = 100 := by
  rw [Core.F64.toRat_fin]
  simp only [Core.F64.signed, Int.cast_natCast]
  refine (div_eq_iff (a := ((100 * Core.F64.unit : Nat) : Rat))
    (b := ((Core.F64.unit : Nat) : Rat)) (c := 100)
    (by exact_mod_cast ne_of_gt Core.F64.unit_pos)).mpr ?_
  rw [show ((100 * Core.F64.unit : Nat) : Rat) = 100 * (Core.F64.unit : Rat) by norm_num]

private theorem one_rat :
    (Core.F64.fin false Core.F64.unit).toRatD = 1 := by
  rw [Core.F64.toRat_fin]
  simp only [Core.F64.signed, Int.cast_natCast]
  refine (div_eq_iff (a := ((Core.F64.unit : Nat) : Rat))
    (b := ((Core.F64.unit : Nat) : Rat)) (c := 1)
    (by exact_mod_cast ne_of_gt Core.F64.unit_pos)).mpr ?_
  rw [one_mul]

theorem total_nonneg (price quantity discount tax : Js.Dbl)
    (hp : 0 ≤ Js.Dbl.toRat price) (hq : 0 ≤ Js.Dbl.toRat quantity)
    (hd : 0 ≤ Js.Dbl.toRat discount) (hd100 : Js.Dbl.toRat discount ≤ 100)
    (ht : 0 ≤ Js.Dbl.toRat tax) :
    totalWithTax price quantity discount tax ⦃ r => 0 ≤ Js.Dbl.toRat r ⦄ := by
  unfold totalWithTax
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, WP.spec_ok]
  rw [Js.Dbl.toRat_eq] at hp hq hd hd100 ht ⊢
  rw [hund_f, one_f]
  apply Core.F64.div_toRat_nonneg _ (by rw [hund_rat]; norm_num)
  apply Core.F64.jsround_toRat_nonneg'
  apply Core.F64.mul_toRat_nonneg _ (by rw [hund_rat]; norm_num)
  apply Core.F64.mul_toRat_nonneg
  · apply Core.F64.mul_toRat_nonneg
    · exact Core.F64.mul_toRat_nonneg hp hq
    · apply Core.F64.sub_toRat_nonneg' (by rw [one_rat]; norm_num)
      rw [one_rat]
      cases hdf : discount.f with
      | fin a X =>
        rw [hdf] at hd hd100
        rw [← hund_rat] at hd100
        exact Core.F64.div_le_unit (Core.F64.mag_le_of_toRatD_le hd hd100)
      | nan =>
        rw [show (Core.F64.nan.div (Core.F64.fin false (100 * Core.F64.unit))).toRatD = 0 from rfl]
        norm_num
      | inf a =>
        rw [show ((Core.F64.inf a).div (Core.F64.fin false (100 * Core.F64.unit))).toRatD = 0 from rfl]
        norm_num
  · apply Core.F64.add_toRat_nonneg (by rw [one_rat]; norm_num)
    cases htf : tax.f with
    | fin a X =>
      rw [htf] at ht
      exact Core.F64.div_toRat_nonneg ht (by rw [hund_rat]; norm_num)
    | nan =>
      rw [show (Core.F64.nan.div (Core.F64.fin false (100 * Core.F64.unit))).toRatD = 0 from rfl]
    | inf a =>
      rw [show ((Core.F64.inf a).div (Core.F64.fin false (100 * Core.F64.unit))).toRatD = 0 from rfl]

theorem whole_cents (price quantity discount tax : Js.Dbl) :
    totalWithTax price quantity discount tax
      ⦃ r => r.f.isFin = true →
        ∃ k : Int, ∃ z : Core.F64,
          r.f = z.div (Core.F64.ofInt 100) ∧ z.toRatD = k ⦄ := by
  unfold totalWithTax
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, WP.spec_ok]
  intro hfin
  have h100 : Core.F64.fin false (100 * Core.F64.unit) = Core.F64.ofInt 100 := by
    decide
  set expr := (((price.f.mul quantity.f).mul
      ((Js.Dbl.lit 4607182418800017408).f.sub (discount.f.div (Js.Dbl.lit 4636737291354636288).f))).mul
    ((Js.Dbl.lit 4607182418800017408).f.add (tax.f.div (Js.Dbl.lit 4636737291354636288).f))).mul
    (Js.Dbl.lit 4636737291354636288).f with hexpr
  cases hjsr : expr.jsround with
  | fin s n =>
    have hxf : expr.isFin = true := by
      rw [← Core.F64.isFin_jsround, hjsr]; rfl
    have hi := Core.F64.jsround_isInt hxf
    rw [hjsr] at hi
    obtain ⟨k, hk⟩ := Core.F64.isInt'_toRatD hi
    rw [hund_f]
    exact ⟨k, Core.F64.fin s n, by rw [h100], hk⟩
  | nan =>
    rw [hjsr, hund_f] at hfin
    simp [Core.F64.div, Core.F64.isFin] at hfin
  | inf a =>
    rw [hjsr, hund_f] at hfin
    simp [Core.F64.div, Core.F64.isFin] at hfin

theorem menu_price_exact :
    totalWithTax (dbl!"12.99") (dbl!"2") (dbl!"10") (dbl!"20")
      ⦃ r => r = dbl!"28.06" ⦄ := by
  have h : totalWithTax (dbl!"12.99") (dbl!"2") (dbl!"10") (dbl!"20")
      = ok (dbl!"28.06") := by
    unfold totalWithTax
    simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, Js.Dbl.lit]
    decide
  rw [h]
  simp [WP.spec_ok]

theorem nan_propagates (quantity discount tax : Js.Dbl) :
    totalWithTax (Js.Dbl.lit 0x7ff8000000000000) quantity discount tax
      ⦃ r => Js.Dbl.isNaN r = true ⦄ := by
  have hn : Js.Dbl.lit 0x7ff8000000000000 = ⟨Core.F64.nan⟩ := by decide
  rw [hn]
  unfold totalWithTax
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, Js.Dbl.lit, Js.Dbl.isNaN,
    Core.F64.mul, Core.F64.sub, Core.F64.add, Core.F64.div, Core.F64.jsround, Core.F64.isNan,
    WP.spec_ok]
  try (split <;> first | (rename_i h; exact absurd h (by decide)) |
    simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, Js.Dbl.isNaN,
      Core.F64.mul, Core.F64.sub, Core.F64.add, Core.F64.div, Core.F64.jsround, Core.F64.isNan,
      WP.spec_ok])

theorem perHead_nonneg (total parts : Js.Dbl)
    (ht : 0 ≤ Js.Dbl.toRat total) (hp : 0 ≤ Js.Dbl.toRat parts) :
    perHead total parts ⦃ r => 0 ≤ Js.Dbl.toRat r ⦄ := by
  unfold perHead
  simp [Js.Dbl.rem, Js.Dbl.sub, Js.Dbl.div, WP.spec_ok]
  rw [Js.Dbl.toRat_eq] at ht hp ⊢
  apply Core.F64.div_toRat_nonneg _ hp
  apply Core.F64.sub_toRat_nonneg' ht
  exact Core.F64.rem_toRat_le ht

theorem effect_signs (rate : Js.Dbl) :
    effect rate ⦃ r => r.f.isNan = true ∨ r.f.isInt' = true ⦄ := by
  unfold effect
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.math, Js.Dbl.lit, WP.spec_ok]
  generalize (rate.f.mul rate.f).sub (Core.F64.ofBits 0x3ff0000000000000) = y
  cases y with
  | nan => exact Or.inl rfl
  | inf s => exact Or.inr (by simp [Core.F64.sign, Core.F64.isInt', Nat.mod_self])
  | fin s n =>
    exact Or.inr (by simp [Core.F64.sign]; split <;>
      simp_all [Core.F64.isInt', Nat.zero_mod, Nat.mod_self])
