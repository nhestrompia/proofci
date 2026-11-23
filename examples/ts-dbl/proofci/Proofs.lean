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
    (hpf : price.f.isFin = true) (hqf : quantity.f.isFin = true)
    (hdf : discount.f.isFin = true) (htf : tax.f.isFin = true)
    (hp : 0 ≤ Js.Dbl.toRat price) (hpB : Js.Dbl.toRat price ≤ 10 ^ 9)
    (hq : 0 ≤ Js.Dbl.toRat quantity) (hqB : Js.Dbl.toRat quantity ≤ 10 ^ 9)
    (hd : 0 ≤ Js.Dbl.toRat discount) (hd100 : Js.Dbl.toRat discount ≤ 100)
    (ht : 0 ≤ Js.Dbl.toRat tax) (htB : Js.Dbl.toRat tax ≤ 1000) :
    totalWithTax price quantity discount tax
      ⦃ r => r.f.isFin = true ∧ 0 ≤ Js.Dbl.toRat r ⦄ := by
  unfold totalWithTax
  simp [Js.Dbl.mul, Js.Dbl.sub, Js.Dbl.add, Js.Dbl.div, Js.Dbl.math, WP.spec_ok]
  rw [Js.Dbl.toRat_eq] at hp hpB hq hqB hd hd100 ht htB ⊢
  have hunitl : (0 : Nat) < Core.F64.unit := Core.F64.unit_pos
  cases hpx : price.f with
  | fin ap Xp =>
    rw [hpx] at hpf hp hpB
    have hXp : Xp ≤ 10 ^ 9 * Core.F64.unit :=
      Core.F64.mag_le_of_toRatD_le hp (by rw [Core.F64.const_mag, show ((10 ^ 9 : Nat) : Rat) = 10 ^ 9 from by norm_num]; exact hpB)
    cases hqx : quantity.f with
    | fin aq Xq =>
      rw [hqx] at hqf hq hqB
      have hXq : Xq ≤ 10 ^ 9 * Core.F64.unit :=
        Core.F64.mag_le_of_toRatD_le hq (by rw [Core.F64.const_mag, show ((10 ^ 9 : Nat) : Rat) = 10 ^ 9 from by norm_num]; exact hqB)
      cases hdx : discount.f with
      | fin ad Xd =>
        rw [hdx] at hdf hd hd100
        have hXd : Xd ≤ 100 * Core.F64.unit :=
          Core.F64.mag_le_of_toRatD_le hd (by rw [Core.F64.const_mag]; exact hd100)
        cases htx : tax.f with
        | fin at_ Xt =>
          rw [htx] at htf ht htB
          have hXt : Xt ≤ 1000 * Core.F64.unit :=
            Core.F64.mag_le_of_toRatD_le ht (by rw [Core.F64.const_mag]; exact htB)
          rw [one_f, hund_f]
          have h10e9u : (10 ^ 9 * Core.F64.unit) * (10 ^ 9 * Core.F64.unit) = (10 ^ 18 * Core.F64.unit) * Core.F64.unit := by ring
          have lim1 : 2 * (10 ^ 18 * Core.F64.unit) + 1 < Core.F64.limit := by
            unfold Core.F64.limit Core.F64.unit; decide
          obtain ⟨m1, hm1, hm1b⟩ := Core.F64.mul_fin (le_trans (Nat.mul_le_mul hXp hXq) (le_of_eq h10e9u)) lim1
          have hd1 : ∃ m, (Core.F64.fin ad Xd).div (Core.F64.fin false (100 * Core.F64.unit)) = Core.F64.fin (ad != false) m ∧ m ≤ 2 * (100 * Core.F64.unit) + 1 :=
            Core.F64.div_fin (show Core.F64.unit ≤ 100 * Core.F64.unit from by unfold Core.F64.unit; decide) hXd (by unfold Core.F64.limit Core.F64.unit; decide)
          obtain ⟨md, hmd, hmdb⟩ := hd1
          have hsf : ∃ s m, (Core.F64.fin false Core.F64.unit).sub (Core.F64.fin (ad != false) md) = Core.F64.fin s m ∧ m ≤ 2 * (202 * Core.F64.unit) + 1 :=
            Core.F64.sub_fin (B := 202 * Core.F64.unit) (show Core.F64.unit + md ≤ 202 * Core.F64.unit from by omega) (by unfold Core.F64.limit Core.F64.unit; decide)
          obtain ⟨ss, ms, hms, hmsb⟩ := hsf
          have hm1b2 : m1 * ms ≤ ((2 * 10 ^ 18 + 1) * 405) * Core.F64.unit * Core.F64.unit := by
            have h1 : m1 ≤ (2 * 10 ^ 18 + 1) * Core.F64.unit := by omega
            have h2 : ms ≤ 405 * Core.F64.unit := by omega
            calc m1 * ms ≤ ((2 * 10 ^ 18 + 1) * Core.F64.unit) * (405 * Core.F64.unit) := Nat.mul_le_mul h1 h2
              _ = ((2 * 10 ^ 18 + 1) * 405) * Core.F64.unit * Core.F64.unit := by ring
          obtain ⟨m2, hm2, hm2b⟩ := Core.F64.mul_fin (le_trans hm1b2 (le_of_eq (by ring : ((2*10^18+1)*405)*Core.F64.unit*Core.F64.unit = ((2*10^18+1)*405*Core.F64.unit)*Core.F64.unit))) (by unfold Core.F64.limit Core.F64.unit; decide)
          have ht1 : ∃ m, (Core.F64.fin at_ Xt).div (Core.F64.fin false (100 * Core.F64.unit)) = Core.F64.fin (at_ != false) m ∧ m ≤ 2 * (1000 * Core.F64.unit) + 1 :=
            Core.F64.div_fin (show Core.F64.unit ≤ 100 * Core.F64.unit from by unfold Core.F64.unit; decide) hXt (by unfold Core.F64.limit Core.F64.unit; decide)
          obtain ⟨mt, hmt, hmtb⟩ := ht1
          obtain ⟨sa, ma, hma, hmab⟩ := Core.F64.add_fin (B := 2002 * Core.F64.unit) (show Core.F64.unit + mt ≤ 2002 * Core.F64.unit from by omega) (by unfold Core.F64.limit Core.F64.unit; decide)
          obtain ⟨m3, hm3, hm3b⟩ := Core.F64.mul_fin (show m2 * ma ≤ ((2 * ((2*10^18+1)*405) + 1) * 4005) * Core.F64.unit * Core.F64.unit from by
            have h1 : m2 ≤ (2 * ((2*10^18+1)*405) + 1) * Core.F64.unit := by omega
            have h2 : ma ≤ 4005 * Core.F64.unit := by omega
            calc m2 * ma ≤ ((2 * ((2*10^18+1)*405) + 1) * Core.F64.unit) * (4005 * Core.F64.unit) := Nat.mul_le_mul h1 h2
              _ = ((2 * ((2*10^18+1)*405) + 1) * 4005) * Core.F64.unit * Core.F64.unit := by ring)
            (by unfold Core.F64.limit Core.F64.unit; decide)
          obtain ⟨m4, hm4, hm4b⟩ := Core.F64.mul_fin (show m3 * (100 * Core.F64.unit) ≤ ((2 * ((2*((2*10^18+1)*405)+1)*4005) + 1) * 100) * Core.F64.unit * Core.F64.unit from by
            have h1 : m3 ≤ (2 * ((2*((2*10^18+1)*405)+1)*4005) + 1) * Core.F64.unit := by omega
            calc m3 * (100 * Core.F64.unit) ≤ ((2 * ((2*((2*10^18+1)*405)+1)*4005) + 1) * Core.F64.unit) * (100 * Core.F64.unit) := Nat.mul_le_mul h1 (Nat.le_refl _)
              _ = ((2 * ((2*((2*10^18+1)*405)+1)*4005) + 1) * 100) * Core.F64.unit * Core.F64.unit := by ring)
            (by unfold Core.F64.limit Core.F64.unit; decide)
          -- jsround: finite, bounded by n + unit
          obtain ⟨mj, hmj, hmjb⟩ :=
            Core.F64.jsround_fin_le (neg := (((ap != aq) != ss) != sa) != false) (n := m4)
          obtain ⟨mr, hmr, hmrb⟩ := Core.F64.div_fin (a := (((ap != aq) != ss) != sa) != false)
            (b := false) (X := mj) (Y := 100 * Core.F64.unit)
            (show Core.F64.unit ≤ 100 * Core.F64.unit from by unfold Core.F64.unit; decide)
            (show mj ≤ (2*((2*((2*((2*10^18+1)*405)+1)*4005)+1)*100) + 2) * Core.F64.unit from by omega)
            (by unfold Core.F64.limit Core.F64.unit; decide)
          -- non-negativity: every operand is finite non-negative, and the only
          -- subtraction is `1 - d/100` with `d/100 ≤ 1`
          have hpnn : 0 ≤ (Core.F64.fin ap Xp).toRatD := hp
          have hqnn : 0 ≤ (Core.F64.fin aq Xq).toRatD := hq
          have hdnn : 0 ≤ (Core.F64.fin ad Xd).toRatD := hd
          have htnn : 0 ≤ (Core.F64.fin at_ Xt).toRatD := ht
          have h1nn : 0 ≤ (Core.F64.fin false Core.F64.unit).toRatD := by
            rw [one_rat]; norm_num
          have h100nn : 0 ≤ (Core.F64.fin false (100 * Core.F64.unit)).toRatD := by
            rw [hund_rat]; norm_num
          have hdv : ((Core.F64.fin ad Xd).div (Core.F64.fin false (100 * Core.F64.unit))).toRatD
              ≤ (Core.F64.fin false Core.F64.unit).toRatD := by
            rw [one_rat]; exact Core.F64.div_le_unit hXd
          have hsubnn := Core.F64.sub_toRat_nonneg' h1nn hdv
          rw [hmd] at hsubnn
          rw [hms] at hsubnn
          have hm1nn := Core.F64.mul_toRat_nonneg hpnn hqnn
          rw [hm1] at hm1nn
          have hm2nn := Core.F64.mul_toRat_nonneg hm1nn hsubnn
          rw [hm2] at hm2nn
          have haddnn := Core.F64.add_toRat_nonneg h1nn (Core.F64.div_toRat_nonneg htnn h100nn)
          rw [hmt] at haddnn
          rw [hma] at haddnn
          have hm3nn := Core.F64.mul_toRat_nonneg hm2nn haddnn
          rw [hm3] at hm3nn
          have hm4nn := Core.F64.mul_toRat_nonneg hm3nn h100nn
          rw [hm4] at hm4nn
          have hmjnn := Core.F64.jsround_toRat_nonneg' hm4nn
          rw [hmj] at hmjnn
          have hmr_nn := Core.F64.div_toRat_nonneg hmjnn h100nn
          rw [hmr] at hmr_nn
          rw [hm1, hmd, hms, hm2, hmt, hma, hm3, hm4, hmj, hmr]
          exact ⟨rfl, hmr_nn⟩
        | nan => rw [htx] at htf; simp [Core.F64.isFin] at htf
        | inf s => rw [htx] at htf; simp [Core.F64.isFin] at htf
      | nan => rw [hdx] at hdf; simp [Core.F64.isFin] at hdf
      | inf s => rw [hdx] at hdf; simp [Core.F64.isFin] at hdf
    | nan => rw [hqx] at hqf; simp [Core.F64.isFin] at hqf
    | inf s => rw [hqx] at hqf; simp [Core.F64.isFin] at hqf
  | nan => rw [hpx] at hpf; simp [Core.F64.isFin] at hpf
  | inf s => rw [hpx] at hpf; simp [Core.F64.isFin] at hpf

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
    (htf : total.f.isFin = true) (hpf : parts.f.isFin = true)
    (ht : 0 ≤ Js.Dbl.toRat total) (htB : Js.Dbl.toRat total ≤ 10 ^ 9)
    (hp : 1 ≤ Js.Dbl.toRat parts) :
    perHead total parts ⦃ r => r.f.isFin = true ∧ 0 ≤ Js.Dbl.toRat r ⦄ := by
  unfold perHead
  simp [Js.Dbl.sub, Js.Dbl.rem, Js.Dbl.div, WP.spec_ok]
  rw [Js.Dbl.toRat_eq] at ht htB hp ⊢
  cases htx : total.f with
  | fin at_ Xt =>
    rw [htx] at htf ht htB
    have hXt : Xt ≤ 10 ^ 9 * Core.F64.unit :=
      Core.F64.mag_le_of_toRatD_le ht (by rw [Core.F64.const_mag, show ((10 ^ 9 : Nat) : Rat) = 10 ^ 9 from by norm_num]; exact htB)
    cases hpx : parts.f with
    | fin ap Xp =>
      rw [hpx] at hpf hp
      have hXp : Core.F64.unit ≤ Xp := Core.F64.unit_le_mag_of_one_le_toRatD hp
      have hXp0 : Xp ≠ 0 := by have := Core.F64.unit_pos; omega
      obtain ⟨mr, hmr, hmrb⟩ := Core.F64.rem_fin (a := at_) (b := ap) (X := Xt) (Y := Xp) hXp0
      obtain ⟨ss, ms, hms, hmsb⟩ := Core.F64.sub_fin (a := at_) (X := Xt) (b := at_) (Y := mr)
        (show Xt + mr ≤ 2 * (10 ^ 9 * Core.F64.unit) from by omega)
        (by unfold Core.F64.limit Core.F64.unit; decide)
      obtain ⟨mo, hmo, hmob⟩ := Core.F64.div_fin (a := ss) (b := ap) (X := ms) (Y := Xp)
        hXp
        (show ms ≤ (4 * 10 ^ 9 + 2) * Core.F64.unit from by have := Core.F64.unit_pos; omega)
        (by unfold Core.F64.limit Core.F64.unit; decide)
      -- non-negativity
      have htnn : 0 ≤ (Core.F64.fin at_ Xt).toRatD := ht
      have hremnn : 0 ≤ ((Core.F64.fin at_ Xt).rem (Core.F64.fin ap Xp)).toRatD := Core.F64.rem_toRat_nonneg htnn
      rw [hmr] at hremnn
      have hle : ((Core.F64.fin at_ Xt).rem (Core.F64.fin ap Xp)).toRatD ≤ (Core.F64.fin at_ Xt).toRatD :=
        Core.F64.rem_toRat_le htnn
      have hsubnn := Core.F64.sub_toRat_nonneg' htnn hle
      rw [hmr] at hsubnn
      rw [hms] at hsubnn
      have hfinnn := Core.F64.div_toRat_nonneg hsubnn (le_trans zero_le_one hp)
      rw [hmo] at hfinnn
      rw [hmr, hms, hmo]
      exact ⟨rfl, hfinnn⟩
    | nan => rw [hpx] at hpf; simp [Core.F64.isFin] at hpf
    | inf s => rw [hpx] at hpf; simp [Core.F64.isFin] at hpf
  | nan => rw [htx] at htf; simp [Core.F64.isFin] at htf
  | inf s => rw [htx] at htf; simp [Core.F64.isFin] at htf

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
