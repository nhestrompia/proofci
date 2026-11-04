import Aeneas
import ProofciJs

open Aeneas Aeneas.Std Result

structure src.phases.MonteCarloSpendingPhase where
  id : Js.Str
  «name» : Js.Str
  fromAge : (Option Js.Num)
  annualWithdrawal : Js.Num
deriving DecidableEq, Repr

def src.phases.getActiveSpendingPhase (resolvedPhases : (List _root_.src.phases.MonteCarloSpendingPhase)) (age : Js.Num) : Result _root_.src.phases.MonteCarloSpendingPhase := do
  let active ← Result.ok ((Js.at_ resolvedPhases (Js.Num.mk (0) (of_decide_eq_true rfl) (of_decide_eq_true rfl))))
  let tmp1 ← Result.ok (resolvedPhases)
  let active_4 ← (Aeneas.Std.loop (fun (state : (List _root_.src.phases.MonteCarloSpendingPhase) × (Option _root_.src.phases.MonteCarloSpendingPhase)) => match state with | (tmp1_1, active_1) => do
    match tmp1_1 with
    | [] =>
      Result.ok (.done active_1)
    | phase :: tmp2 =>
      match phase.fromAge with
      | none =>
        let active_2 ← Result.ok ((some phase))
        Result.ok (.cont (tmp2, active_2))
      | some tmp3 =>
        if tmp3.val ≤ age.val then
          let active_3 ← Result.ok ((some phase))
          Result.ok (.cont (tmp2, active_3))
        else
          Result.ok (.done active_1)
  ) (tmp1, active) : Result ((Option _root_.src.phases.MonteCarloSpendingPhase)))
  let tmp4 ← Js.unwrap active_4
  Result.ok tmp4

structure Proofci.Inline.R9365a59415 where
  floorPriceX96 : Int
  tickSpacing : Int
deriving DecidableEq, Repr

def src.constants.AUCTION_TICK_DIVISOR : Result Int := do
  Result.ok (100 : Int)

def src.config.price.deriveAuctionTickSpacing (floorPriceX96 : Int) : Result Int := do
  let tmp1 ← _root_.src.constants.AUCTION_TICK_DIVISOR
  let tmp2 ← Js.bdiv floorPriceX96 tmp1
  let tickSpacing ← Result.ok (tmp2)
  let tmp3 ← if tickSpacing > (0 : Int) then
      Result.ok tickSpacing
    else
      Result.ok (1 : Int)
  Result.ok tmp3

def src.config.price.deriveAuctionPricing (rawFloorPriceX96 : Int) : Result _root_.Proofci.Inline.R9365a59415 := do
  let tmp1 ← _root_.src.config.price.deriveAuctionTickSpacing rawFloorPriceX96
  let tickSpacing ← Result.ok (tmp1)
  let tmp2 ← Js.brem rawFloorPriceX96 tickSpacing
  Result.ok ({ floorPriceX96 := (rawFloorPriceX96 - tmp2), tickSpacing := tickSpacing } : _root_.Proofci.Inline.R9365a59415)

structure src.ledger.Accounts where
  «from» : Js.Num
  «to» : Js.Num
deriving DecidableEq, Repr

def src.ledger.transfer (accounts : _root_.src.ledger.Accounts) (amount : Js.Num) : Result (Option _root_.src.ledger.Accounts) := do
  if (amount.val ≤ 0) ∨ (amount.val > accounts.«from».val) then
    Result.ok none
  else
    let tmp1 ← Js.sub accounts.«from» amount
    let tmp2 ← Js.add accounts.«to» amount
    Result.ok (some ({ «from» := tmp1, «to» := tmp2 } : _root_.src.ledger.Accounts))

def src.ledger.sumAmounts (amounts : (List Js.Num)) : Result Js.Num := do
  let total ← Result.ok ((Js.Num.mk (0) (of_decide_eq_true rfl) (of_decide_eq_true rfl)))
  let tmp1 ← Result.ok (amounts)
  let total_3 ← (Aeneas.Std.loop (fun (state : (List Js.Num) × Js.Num) => match state with | (tmp1_1, total_1) => do
    match tmp1_1 with
    | [] =>
      Result.ok (.done total_1)
    | amount :: tmp2 =>
      let tmp3 ← Js.add total_1 amount
      let total_2 ← Result.ok (tmp3)
      Result.ok (.cont (tmp2, total_2))
  ) (tmp1, total) : Result (Js.Num))
  Result.ok total_3

