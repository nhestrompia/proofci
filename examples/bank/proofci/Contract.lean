import Bank
open Aeneas Aeneas.Std Result bank

/-- Withdrawing more than the balance is rejected. -/
theorem withdraw_rejects_overdraft (balance amount : Std.U64) (h : balance.val < amount.val) :
    withdraw balance amount = ok none := by sorry

/-- Otherwise the new balance is exactly the difference (and nothing panics). -/
theorem withdraw_exact (balance amount : Std.U64) (h : amount.val ≤ balance.val) :
    withdraw balance amount ⦃ r => ∃ b, r = some b ∧ b.val = balance.val - amount.val ⦄ := by sorry
