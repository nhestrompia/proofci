import CandidateCheck
theorem contract : ¬ (∀ x : Nat, (x < 3) → target x = x) ∧ (let x : Nat := 0; (x < 3) ∧ ¬ (target x = x)) := by
  constructor
  · intro h; exact Nat.noConfusion (h 0 (Nat.zero_lt_succ 2))
  · dsimp; constructor
    · exact Nat.zero_lt_succ 2
    · intro h; exact Nat.noConfusion h
