import Core
open Core
set_option maxRecDepth 4000
namespace Gen

def src_phases_getActiveSpendingPhase : Fn := { params := ["resolvedPhases", "age"], body := [
    .set "active" (.index (.var "resolvedPhases") (.lit (.num 0))),
    .forOf "phase" (.var "resolvedPhases") [.ite (.or (.isNullish (.field (.var "phase") "fromAge")) (.bin .le (.field (.var "phase") "fromAge") (.var "age"))) [.set "active" (.var "phase")] [.brk]],
    .ret (.var "active")] }

def src_config_price_deriveAuctionPricing : Fn := { params := ["rawFloorPriceX96"], body := [
    .set "tickSpacing" (.call "src_config_price_deriveAuctionTickSpacing" [.var "rawFloorPriceX96"]),
    .ret (.record [("floorPriceX96", .bin .sub (.var "rawFloorPriceX96") (.bin .rem (.var "rawFloorPriceX96") (.var "tickSpacing"))), ("tickSpacing", .var "tickSpacing")])] }

def src_ledger_transfer : Fn := { params := ["accounts", "amount"], body := [
    .ite (.or (.bin .le (.var "amount") (.lit (.num 0))) (.bin .gt (.var "amount") (.field (.var "accounts") "from"))) [.ret (.lit .null)] [],
    .ret (.record [("from", .bin .sub (.field (.var "accounts") "from") (.var "amount")), ("to", .bin .add (.field (.var "accounts") "to") (.var "amount"))])] }

def src_ledger_sumAmounts : Fn := { params := ["amounts"], body := [
    .set "total" (.lit (.num 0)),
    .forOf "amount" (.var "amounts") [.set "total" (.bin .add (.var "total") (.var "amount"))],
    .ret (.var "total")] }

def src_shared_moveMoney : Fn := { params := ["from", "to", "amount"], body := [
    .setField (.var "from") "balance" (.bin .sub (.field (.var "from") "balance") (.var "amount")),
    .setField (.var "to") "balance" (.bin .add (.field (.var "to") "balance") (.var "amount"))] }

def src_shared_moveMoneyStale : Fn := { params := ["from", "to", "amount"], body := [
    .set "a" (.field (.var "from") "balance"),
    .set "b" (.field (.var "to") "balance"),
    .setField (.var "from") "balance" (.bin .sub (.var "a") (.var "amount")),
    .setField (.var "to") "balance" (.bin .add (.var "b") (.var "amount"))] }

def src_config_price_deriveAuctionTickSpacing : Fn := { params := ["floorPriceX96"], body := [
    .set "tickSpacing" (.bin .div (.var "floorPriceX96") (.lit (.big 100))),
    .ret (.cond (.bin .gt (.var "tickSpacing") (.lit (.big 0))) (.var "tickSpacing") (.lit (.big 1)))] }

def prog : Prog := fun name => match name with
  | "src_phases_getActiveSpendingPhase" => some src_phases_getActiveSpendingPhase
  | "src_config_price_deriveAuctionPricing" => some src_config_price_deriveAuctionPricing
  | "src_ledger_transfer" => some src_ledger_transfer
  | "src_ledger_sumAmounts" => some src_ledger_sumAmounts
  | "src_shared_moveMoney" => some src_shared_moveMoney
  | "src_shared_moveMoneyStale" => some src_shared_moveMoneyStale
  | "src_config_price_deriveAuctionTickSpacing" => some src_config_price_deriveAuctionTickSpacing
  | _ => none

end Gen
