import DateFnsExcerpt
open Aeneas Aeneas.Std Result
open src.parse._lib.utils src.parseISO.index

/-- The Gregorian rule: divisible by 4, and a century only when divisible by 400. -/
theorem leap_year_rule (year : Js.Num) :
    src.parse._lib.utils.isLeapYearIndex year ⦃ r =>
      r = true ↔ (4 ∣ year.val ∧ (100 ∣ year.val → 400 ∣ year.val)) ⦄ := by sorry

/-- Day 365 is always a valid day of the year, and day 366 only in a leap year. -/
theorem day_of_year_range (year dayOfYear : Js.Num) :
    validateDayOfYearDate year dayOfYear ⦃ r =>
      r = true ↔ ((1 ≤ dayOfYear.val ∧ dayOfYear.val ≤ 365) ∨
        (dayOfYear.val = 366 ∧ 4 ∣ year.val ∧ (100 ∣ year.val → 400 ∣ year.val))) ⦄ := by sorry

/-- Hour 24 is accepted only as exactly 24:00:00 (end of day). -/
theorem midnight_24_only (minutes seconds : Js.Num) :
    validateTime (Js.Num.mk 24 (of_decide_eq_true rfl) (of_decide_eq_true rfl)) minutes seconds ⦃ r =>
      r = true ↔ (minutes.val = 0 ∧ seconds.val = 0) ⦄ := by sorry

/-- An accepted time is a real time of day: at most 24:00:00, minutes and seconds below 60. -/
theorem valid_time_in_range (hours minutes seconds : Js.Num) :
    validateTime hours minutes seconds ⦃ r =>
      r = true → (0 ≤ hours.val ∧ hours.val ≤ 24 ∧ 0 ≤ minutes.val ∧ minutes.val < 60 ∧
        0 ≤ seconds.val ∧ seconds.val < 60) ⦄ := by sorry
