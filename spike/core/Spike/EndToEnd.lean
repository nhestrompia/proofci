import Spike.Bridges
open Core Aeneas Aeneas.Std Result Gen src.ledger

/-! The whole chain: a user's proof on the typed view, carried through a generated bridge
to a statement about what the JavaScript does, heap and all. -/

/-- The user's theorem, unchanged from `examples/ts-bank`. -/
theorem transfer_conserves (a : Accounts) (amount : Js.Num)
    (hfrom : 0 ≤ a.from.val) (hto : 0 ≤ a.to.val)
    (htotal : a.from.val + a.to.val ≤ 9007199254740991) :
    transfer a amount ⦃ r => ∀ b, r = some b →
      b.from.val + b.to.val = a.from.val + a.to.val ∧ 0 ≤ b.from.val ⦄ := by
  unfold transfer
  step*

theorem spec_ok_inv {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) : ∃ r, m = ok r ∧ P r := by
  revert h
  refine Result.cases (motive := fun m => m ⦃ P ⦄ → ∃ r, m = ok r ∧ P r) m ?_ ?_ ?_
  · intro a h; exact ⟨a, rfl, by simpa [WP.spec_ok] using h⟩
  · intro i k h; simp [WP.spec_vis] at h
  · intro h; simp [WP.spec_div] at h

/-- What the theorem says once it reaches JavaScript: for any values that encode these
accounts, `transfer` runs and returns a value that encodes a result with the same total. -/
theorem transfer_conserves_in_js {h} {a : Accounts} {amount : Js.Num} {va vamt}
    (ha : Enc.enc h a va) (hn : Enc.enc h amount vamt)
    (hfrom : 0 ≤ a.from.val) (hto : 0 ≤ a.to.val)
    (htotal : a.from.val + a.to.val ≤ 9007199254740991) :
    WpRun prog src_ledger_transfer [va, vamt] h fun v s => ∃ r, Enc.enc s.heap r v ∧ ∀ b : Accounts, r = some b →
      b.from.val + b.to.val = a.from.val + a.to.val ∧ 0 ≤ b.from.val := by
  obtain ⟨r, hr, hP⟩ := spec_ok_inv (transfer_conserves a amount hfrom hto htotal)
  exact (src_ledger_transfer_bridge ha hn hr).mono fun _ _ ⟨_, he⟩ => ⟨r, he, hP⟩

#print axioms transfer_conserves_in_js
