/-
Protected contract. ProofCI reads this file from the base branch, so a pull
request cannot change what has to be proved. Every statement ends in `sorry`;
the proofs live in Proofs.lean.

`f x ⦃ r => P r ⦄` means: the call succeeds (no panic, no overflow) and its
result `r` satisfies `P`.
-/
import Ledger
open Aeneas Aeneas.Std Result ledger

/-- The fee never exceeds the amount, and computing it never overflows. -/
theorem fee_capped (amount fee_bps : Std.U64) :
    calculate_fee amount fee_bps ⦃ fee => fee.val ≤ amount.val ⦄ := by sorry

/-- A zero amount is never charged a fee. -/
theorem zero_amount_no_fee (fee_bps : Std.U64) :
    calculate_fee 0#u64 fee_bps ⦃ fee => fee.val = 0 ⦄ := by sorry

/-- A transfer never panics, and a successful one conserves the total balance. -/
theorem transfer_conserves (a : Accounts) (amount : Std.U64) :
    transfer a amount ⦃ r => ∀ b, r = some b → b.from.val + b.to.val = a.from.val + a.to.val ⦄ := by
  sorry

/-- Sending more than the sender holds is rejected. -/
theorem transfer_rejects_overdraft (a : Accounts) (amount : Std.U64) (h : a.from.val < amount.val) :
    transfer a amount = ok none := by sorry
