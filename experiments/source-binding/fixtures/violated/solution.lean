import CandidateCheck
theorem contract : ¬ (∀ x : Nat, target x = x + 0) ∧ (let x : Nat := 0; ¬ (target x = x + 0)) := by
  constructor
  · intro h; exact Nat.noConfusion (h 0)
  · dsimp; intro h; exact Nat.noConfusion h
