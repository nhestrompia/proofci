import CandidateCheck
theorem contract : ¬ (∀ x : Nat, target x = x + 0) := by
  intro h; exact Nat.noConfusion (h 0)
