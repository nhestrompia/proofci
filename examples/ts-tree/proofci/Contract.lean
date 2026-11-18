import TsTree
open Aeneas Aeneas.Std Result

/-! The view of `src/tree.ts`: `Item`, `Tree` and `Json` are inductive types, and the functions
that walk them are recursive. -/

/-- `prepend` puts the new item in front of the list it was given. -/
theorem prepend_links (list : Option src.tree.Item) (value : Js.Num) :
    src.tree.prepend list value = ok ⟨value, list⟩ := by
  sorry

/-- The empty list adds up to zero. -/
theorem total_empty : ∃ n, src.tree.total none = ok n ∧ n.val = 0 := by
  sorry

/-- A list of one item adds up to that item. -/
theorem total_one (v : Js.Num) : src.tree.total (some ⟨v, none⟩) = ok v := by
  sorry

/-- A tree with no children has size one. -/
theorem size_leaf (label : Js.Str) : ∃ n, src.tree.size ⟨label, []⟩ = ok n ∧ n.val = 1 := by
  sorry

/-- The leaves of a pair are the leaves of its two halves, added. -/
theorem leaves_pair (l r : src.tree.Json) (a b : Js.Num)
    (hl : src.tree.leaves l = ok a) (hr : src.tree.leaves r = ok b) :
    src.tree.leaves (.pair l r) = Js.add a b := by
  sorry
