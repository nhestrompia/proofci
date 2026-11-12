import DateFnsExcerpt
open Aeneas Aeneas.Std Result
open src.parse._lib.utils src.parseISO.index

/-- `omega` knows `∣` by a literal, but not `Int.tmod`. -/
theorem tmod_zero_iff (x d : Int) : Int.tmod x d = 0 ↔ d ∣ x := Int.dvd_iff_tmod_eq_zero.symm

theorem leap_year_rule (year : Js.Num) :
    src.parse._lib.utils.isLeapYearIndex year ⦃ r =>
      r = true ↔ (4 ∣ year.val ∧ (100 ∣ year.val → 400 ∣ year.val)) ⦄ := by
  unfold src.parse._lib.utils.isLeapYearIndex
  step*
  split
  · rename_i h
    have h400 : 400 ∣ year.val := (tmod_zero_iff _ _).mp (by omega)
    simp [WP.spec_ok]
    omega
  · rename_i h
    have h400 : ¬ 400 ∣ year.val := fun hd => h (by rw [tmp1_post]; exact (tmod_zero_iff _ _).mpr hd)
    step*
    split
    · rename_i h4
      have h4' : 4 ∣ year.val := (tmod_zero_iff _ _).mp (by omega)
      step*
      have h100 : x.val = 0 ↔ 100 ∣ year.val := by rw [x_post]; exact tmod_zero_iff _ _
      simp [WP.spec_ok]
      omega
    · rename_i h4
      have h4' : ¬ 4 ∣ year.val := fun hd => h4 (by rw [x_post]; exact (tmod_zero_iff _ _).mpr hd)
      simp [WP.spec_ok]
      omega

@[step] theorem leap_iso_spec (year : Js.Num) :
    src.parseISO.index.isLeapYearIndex year ⦃ r =>
      r = true ↔ (4 ∣ year.val ∧ (100 ∣ year.val → 400 ∣ year.val)) ⦄ := by
  unfold src.parseISO.index.isLeapYearIndex
  step*
  split
  · rename_i h
    have h400 : 400 ∣ year.val := (tmod_zero_iff _ _).mp (by omega)
    simp [WP.spec_ok]
    omega
  · rename_i h
    have h400 : ¬ 400 ∣ year.val := fun hd => h (by rw [tmp1_post]; exact (tmod_zero_iff _ _).mpr hd)
    step*
    split
    · rename_i h4
      have h4' : 4 ∣ year.val := (tmod_zero_iff _ _).mp (by omega)
      step*
      have h100 : x.val = 0 ↔ 100 ∣ year.val := by rw [x_post]; exact tmod_zero_iff _ _
      simp [WP.spec_ok]
      omega
    · rename_i h4
      have h4' : ¬ 4 ∣ year.val := fun hd => h4 (by rw [x_post]; exact (tmod_zero_iff _ _).mpr hd)
      simp [WP.spec_ok]
      omega

theorem day_of_year_range (year dayOfYear : Js.Num) :
    validateDayOfYearDate year dayOfYear ⦃ r =>
      r = true ↔ ((1 ≤ dayOfYear.val ∧ dayOfYear.val ≤ 365) ∨
        (dayOfYear.val = 366 ∧ 4 ∣ year.val ∧ (100 ∣ year.val → 400 ∣ year.val))) ⦄ := by
  unfold validateDayOfYearDate
  split
  · step*
    split
    · rename_i h2
      simp_all [WP.spec_ok]
      omega
    · rename_i h2
      simp_all [WP.spec_ok]
  · simp_all [WP.spec_ok]
    omega

theorem midnight_24_only (minutes seconds : Js.Num) :
    validateTime (Js.Num.mk 24 (of_decide_eq_true rfl) (of_decide_eq_true rfl)) minutes seconds ⦃ r =>
      r = true ↔ (minutes.val = 0 ∧ seconds.val = 0) ⦄ := by
  unfold validateTime
  simp [WP.spec_ok]

theorem valid_time_in_range (hours minutes seconds : Js.Num) :
    validateTime hours minutes seconds ⦃ r =>
      r = true → (0 ≤ hours.val ∧ hours.val ≤ 24 ∧ 0 ≤ minutes.val ∧ minutes.val < 60 ∧
        0 ≤ seconds.val ∧ seconds.val < 60) ⦄ := by
  unfold validateTime
  split
  · simp_all [WP.spec_ok]
  · simp_all [WP.spec_ok]
    omega
