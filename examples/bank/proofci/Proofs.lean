import Bank
import ProofciSpecs     -- extra step lemmas shipped with ProofCI (optional)
open Aeneas Aeneas.Std Result bank

theorem withdraw_rejects_overdraft (balance amount : Std.U64) (h : balance.val < amount.val) :
    withdraw balance amount = ok none := by
  unfold withdraw
  rw [if_pos (by scalar_tac)]   -- `amount > balance` holds, so take the first branch

theorem withdraw_exact (balance amount : Std.U64) (h : amount.val ≤ balance.val) :
    withdraw balance amount ⦃ r => ∃ b, r = some b ∧ b.val = balance.val - amount.val ⦄ := by
  unfold withdraw
  step*
