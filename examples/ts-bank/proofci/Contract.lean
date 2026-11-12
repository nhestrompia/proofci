import TsBank
open Aeneas Aeneas.Std Result src.ledger

/-- The fee never exceeds the cap, and computing it stays in safe integers. -/
theorem fee_capped (amount rate : Js.Num) (h : amount.val * rate.val ≤ 9007199254740991)
    (h' : -9007199254740991 ≤ amount.val * rate.val) :
    calculateFee amount rate ⦃ fee => fee.val ≤ 500 ⦄ := by sorry

/-- A successful transfer moves money without creating or destroying any. -/
theorem transfer_conserves (a : Accounts) (amount : Js.Num)
    (hfrom : 0 ≤ a.from.val) (hto : 0 ≤ a.to.val)
    (htotal : a.from.val + a.to.val ≤ 9007199254740991) :
    transfer a amount ⦃ r => ∀ b, r = some b →
      b.from.val + b.to.val = a.from.val + a.to.val ∧ 0 ≤ b.from.val ⦄ := by sorry

/-- A transfer larger than the balance is refused. -/
theorem transfer_rejects_overdraft (a : Accounts) (amount : Js.Num) (h : a.from.val < amount.val) :
    transfer a amount = ok none := by sorry

/-- Adding up amounts gives their exact total, without losing precision. -/
theorem sum_exact (xs : List Js.Num) (hn : ∀ x ∈ xs, 0 ≤ x.val)
    (h : Js.total xs ≤ 9007199254740991) :
    sumAmounts xs ⦃ r => r.val = Js.total xs ⦄ := by sorry
