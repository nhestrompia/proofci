import TsPackages
open Aeneas Aeneas.Std Result src.longitude

/-- A longitude within one turn of the range is brought into -180..180. A position
needs a longitude: on an empty one the JavaScript returns `undefined`, so nothing
is claimed there. -/
theorem wrap_longitude_in_range (x : Js.Num) (rest : List Js.Num)
    (h : -540 ≤ x.val ∧ x.val ≤ 540) :
    wrapLongitude (x :: rest) ⦃ r => -180 ≤ r.val ∧ r.val ≤ 180 ⦄ := by sorry
