import TsAssumes
open Aeneas Aeneas.Std Result src.label

/-- A label is a tag followed by at least one character, assuming `slug` succeeds and
    never returns an empty string. The hypothesis is part of the guarantee, so a pull
    request can't change what is assumed. -/
theorem label_tagged (title : Js.Str)
    (slug_nonempty : ∃ s, Proofci.Assumed.slug_maker.slug title = ok s ∧ s ≠ []) :
    label title ⦃ r => r.head? = some 35 ∧ 2 ≤ r.length ⦄ := by sorry
