import Dyn

namespace Bank
open Core Dyn

set_option maxRecDepth 4096

abbrev calculateFee.pre (amount' : Val) (rateBps' : Val) (h : Heap) : Prop :=
  Is h .num amount' ∧
  Is h .num rateBps'
def calculateFee (amount' : Val) (rateBps' : Val) : M Val := do
  return (← (do prim .min [(← (do math F64.floor (← (do bin .div (← (do bin .mul amount' rateBps')) (num 10000))))), (num 500)]))
abbrev transfer.pre (accounts' : Val) (amount' : Val) (h : Heap) : Prop :=
  Is h (.obj [("from", .num), ("to", .num)]) accounts' ∧
  Is h .num amount'
def transfer (accounts' : Val) (amount' : Val) : M Val := do
  if truthy (← (do let a1 := (← (do bin .le amount' (num 0))); if truthy a1 then pure a1 else (do bin .gt amount' (← (do (fun o => field o "from") accounts'))))) then
    return .null
  return (← (do let f2 := (← (do bin .sub (← (do (fun o => field o "from") accounts')) amount')); let f3 := (← (do bin .add (← (do (fun o => field o "to") accounts')) amount')); record [("from", f2), ("to", f3)]))
abbrev sumAmounts.pre (amounts' : Val) (h : Heap) : Prop :=
  Is h (.arr .num) amounts'
def sumAmounts (amounts' : Val) : M Val := do
  let mut total' := (num 0)
  for amount' in (← iter amounts') do
    total' ← (bin .add total' amount')
  return total'
end Bank
