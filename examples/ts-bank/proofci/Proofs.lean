import TsBank
open Aeneas Aeneas.Std Result src.ledger

theorem fee_capped (amount rate : Js.Num) (h : amount.val * rate.val ≤ 9007199254740991)
    (h' : -9007199254740991 ≤ amount.val * rate.val) :
    calculateFee amount rate ⦃ fee => fee.val ≤ 500 ⦄ := by
  unfold calculateFee BASIS_POINTS MAX_FEE
  step*
  simp only [Js.min_val]
  omega

theorem transfer_conserves (a : Accounts) (amount : Js.Num)
    (hfrom : 0 ≤ a.from.val) (hto : 0 ≤ a.to.val)
    (htotal : a.from.val + a.to.val ≤ 9007199254740991) :
    transfer a amount ⦃ r => ∀ b, r = some b →
      b.from.val + b.to.val = a.from.val + a.to.val ∧ 0 ≤ b.from.val ⦄ := by
  unfold transfer
  step*

theorem transfer_rejects_overdraft (a : Accounts) (amount : Js.Num) (h : a.from.val < amount.val) :
    transfer a amount = ok none := by
  unfold transfer
  rw [if_pos (Or.inr h)]
