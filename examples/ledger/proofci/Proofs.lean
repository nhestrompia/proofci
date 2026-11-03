/- Proofs of the guarantees in Contract.lean. Each theorem must restate the
   contract statement exactly; ProofCI checks this with `lake comparator`. -/
import Ledger
open Aeneas Aeneas.Std Result ledger

theorem fee_arith (a b : Nat) (hb : b ≤ 10000) :
    a / 10000 * b + a % 10000 * b / 10000 ≤ a := by
  have h1 : a / 10000 * b ≤ a / 10000 * 10000 := Nat.mul_le_mul_left _ hb
  have h2 : a % 10000 * b / 10000 ≤ a % 10000 := by
    apply Nat.div_le_of_le_mul
    calc a % 10000 * b ≤ a % 10000 * 10000 := Nat.mul_le_mul_left _ hb
      _ = 10000 * (a % 10000) := Nat.mul_comm _ _
  have h3 := Nat.div_add_mod a 10000
  omega

theorem fee_head (a b : Nat) (hb : b ≤ 10000) : a / 10000 * b ≤ a := by
  have := fee_arith a b hb
  omega

theorem fee_capped (amount fee_bps : Std.U64) :
    calculate_fee amount fee_bps ⦃ fee => fee.val ≤ amount.val ⦄ := by
  unfold calculate_fee
  have hD : BPS_DENOMINATOR.val = 10000 := by simp [BPS_DENOMINATOR]
  have hA : amount.val ≤ U64.max := by scalar_tac
  split
  · step*
  · rename_i hle
    have hb : fee_bps.val ≤ 10000 := by simp only [gt_iff_lt, not_lt] at hle; scalar_tac
    step*
    all_goals
      simp only [*] at *
      first
        | (have := fee_head amount.val fee_bps.val hb; omega)
        | (have := fee_arith amount.val fee_bps.val hb; omega)

theorem rmax_eq : U64.rMax = U64.max := by simp [U64.rMax, U64.max, U64.numBits]

theorem zero_amount_no_fee (fee_bps : Std.U64) :
    calculate_fee 0#u64 fee_bps ⦃ fee => fee.val = 0 ⦄ := by
  unfold calculate_fee
  have hD : BPS_DENOMINATOR.val = 10000 := by simp [BPS_DENOMINATOR]
  split
  all_goals
    step*

theorem transfer_conserves (a : Accounts) (amount : Std.U64) :
    transfer a amount ⦃ r => ∀ b, r = some b → b.from.val + b.to.val = a.from.val + a.to.val ⦄ := by
  unfold transfer
  have hM := rmax_eq
  step*

theorem transfer_rejects_overdraft (a : Accounts) (amount : Std.U64) (h : a.from.val < amount.val) :
    transfer a amount = ok none := by
  unfold transfer
  have : amount > a.from := by scalar_tac
  simp [this]
