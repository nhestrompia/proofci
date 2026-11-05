import Core
open Core
set_option maxRecDepth 4000
namespace Gen

def src_features_amountOf : Fn := { params := ["x"], body := [
    .ite (.bin .eq (.typeOf (.var "x")) (.lit (.str [110, 117, 109, 98, 101, 114]))) [.ret (.var "x")] [],
    .ite (.bin .eq (.typeOf (.var "x")) (.lit (.str [115, 116, 114, 105, 110, 103]))) [.ret (.length (.var "x"))] [],
    .ret (.lit (.num (F64.ofInt (0))))] }

def src_features_mapGrows : Fn := { params := ["xs"], body := [
    .set "__scope" (.record [("xs", .var "xs")]),
    .ret (.call "src_prelude_jsMap" [.field (.var "__scope") "xs", .closure "src_features_mapGrows_lambda0" (.record [("__up", .var "__scope")])])] }

def src_features_mapShrinks : Fn := { params := ["xs"], body := [
    .set "__scope" (.record [("xs", .var "xs")]),
    .ret (.call "src_prelude_jsMap" [.field (.var "__scope") "xs", .closure "src_features_mapShrinks_lambda1" (.record [("__up", .var "__scope")])])] }

def src_features_clamp01 : Fn := { params := ["x"], body := [
    .ite (.bin .lt (.var "x") (.lit (.num (F64.ofInt (0))))) [.ret (.lit (.num (F64.ofInt (0))))] [],
    .ite (.bin .gt (.var "x") (.lit (.num (F64.ofInt (1))))) [.ret (.lit (.num (F64.ofInt (1))))] [],
    .ret (.var "x")] }

def src_features_overrideSeen : Fn := { params := [], body := [
    .set "s" (.call "Sub.__new" []),
    .ret (.callM (.var "s") "g" [])] }

def src_features_counterTwice : Fn := { params := ["start"], body := [
    .set "__scope" (.record []),
    .setField (.var "__scope") "n" (.var "start"),
    .set "bump" (.closure "src_features_counterTwice_lambda2" (.record [("__up", .var "__scope")])),
    .set "out" (.array []),
    .push (.var "out") (.callV (.var "bump") []),
    .push (.var "out") (.callV (.var "bump") []),
    .setField (.var "__scope") "n" (.bin .add (.field (.var "__scope") "n") (.lit (.num (F64.ofInt (10))))),
    .push (.var "out") (.callV (.var "bump") []),
    .ret (.var "out")] }

def src_features_loopCaptures_loop0 : List Stmt := [.push (.var "fs") (.closure "src_features_loopCaptures_lambda3" (.record [("__up", .var "__scope"), ("x", .var "x")]))]

def src_features_loopCaptures_loop1 : List Stmt := [.set "total" (.bin .add (.var "total") (.callV (.var "f") []))]

def src_features_loopCaptures : Fn := { params := ["xs"], body := [
    .set "__scope" (.record []),
    .set "fs" (.array []),
    .forOf "x" (.var "xs") src_features_loopCaptures_loop0,
    .set "total" (.lit (.num (F64.ofInt (0)))),
    .forOf "f" (.var "fs") src_features_loopCaptures_loop1,
    .ret (.var "total")] }

def src_features_scaled : Fn := { params := ["xs", "k"], body := [
    .set "__scope" (.record [("k", .var "k")]),
    .ret (.call "src_prelude_jsMap" [.var "xs", .closure "src_features_scaled_lambda4" (.record [("__up", .var "__scope")])])] }

def src_features_indexed : Fn := { params := ["xs"], body := [
    .set "__scope" (.record []),
    .ret (.call "src_prelude_jsMap" [.var "xs", .closure "src_features_indexed_lambda5" (.record [("__up", .var "__scope")])])] }

def src_features_positives : Fn := { params := ["xs"], body := [
    .set "__scope" (.record []),
    .ret (.call "src_prelude_jsFilter" [.var "xs", .closure "src_features_positives_lambda6" (.record [("__up", .var "__scope")])])] }

def src_features_total : Fn := { params := ["xs"], body := [
    .set "__scope" (.record []),
    .ret (.call "src_prelude_jsReduce" [.var "xs", .closure "src_features_total_lambda7" (.record [("__up", .var "__scope")]), .lit (.num (F64.ofInt (0)))])] }

def src_features_anyOver : Fn := { params := ["xs", "limit"], body := [
    .set "__scope" (.record [("limit", .var "limit")]),
    .ret (.call "src_prelude_jsSome" [.var "xs", .closure "src_features_anyOver_lambda8" (.record [("__up", .var "__scope")])])] }

def src_features_firstNegative_loop0 : List Stmt := [.ite (.bin .lt (.var "x") (.lit (.num (F64.ofInt (0))))) [.ret (.var "x")] []]

def src_features_firstNegative : Fn := { params := ["xs"], body := [
    .forOf "x" (.var "xs") src_features_firstNegative_loop0,
    .ret (.lit .null)] }

def src_features_positivesLoop_loop0 : List Stmt := [.ite (.bin .gt (.var "x") (.lit (.num (F64.ofInt (0))))) [.push (.var "out") (.var "x")] []]

def src_features_positivesLoop : Fn := { params := ["xs"], body := [
    .set "out" (.array []),
    .forOf "x" (.var "xs") src_features_positivesLoop_loop0,
    .ret (.var "out")] }

def src_features_sumPlusOne : Fn := { params := ["xs"], body := [
    .ret (.bin .add (.call "src_features_sumAll" [.var "xs"]) (.lit (.num (F64.ofInt (1)))))] }

def src_features_dispatch : Fn := { params := ["n"], body := [
    .set "a" (.call "Shape.__new" [.var "n"]),
    .set "b" (.call "Doubled.__new" [.var "n"]),
    .ret (.bin .add (.bin .mul (.callM (.var "a") "describe" []) (.lit (.num (F64.ofInt (1000))))) (.callM (.var "b") "describe" []))] }

def src_features_growBoth : Fn := { params := ["n"], body := [
    .set "s" (.call "Shape.__new" [.var "n"]),
    .set "same" (.var "s"),
    .setField (.var "same") "size" (.bin .add (.field (.var "same") "size") (.lit (.num (F64.ofInt (1))))),
    .ret (.callM (.var "s") "area" [])] }

def src_features_treeSum : Fn := { params := ["t"], body := [
    .ite (.bin .eq (.var "t") (.lit .null)) [.ret (.lit (.num (F64.ofInt (0))))] [],
    .ret (.bin .add (.bin .add (.field (.var "t") "value") (.call "src_features_treeSum" [.field (.var "t") "left"])) (.call "src_features_treeSum" [.field (.var "t") "right"]))] }

def src_async_withdrawStale_segs : List (List Stmt) := [[.set "b" (.field (.var "a") "balance"), .push (.field (.var "a") "log") (.var "amount")],
  [.setField (.var "a") "balance" (.bin .sub (.var "b") (.var "amount")), .push (.field (.var "a") "log") (.neg (.var "amount"))]]

def src_async_withdrawStale : Fn := { params := ["a", "amount"], body := [] }

def src_async_withdrawSafe_segs : List (List Stmt) := [[.push (.field (.var "a") "log") (.var "amount")],
  [.setField (.var "a") "balance" (.bin .sub (.field (.var "a") "balance") (.var "amount")), .push (.field (.var "a") "log") (.neg (.var "amount"))]]

def src_async_withdrawSafe : Fn := { params := ["a", "amount"], body := [] }

def src_async_twoWaits_segs : List (List Stmt) := [[.push (.field (.var "a") "log") (.var "amount")],
  [.push (.field (.var "a") "log") (.bin .add (.var "amount") (.lit (.num (F64.ofInt (1)))))],
  [.push (.field (.var "a") "log") (.bin .add (.var "amount") (.lit (.num (F64.ofInt (2)))))]]

def src_async_twoWaits : Fn := { params := ["a", "amount"], body := [] }

def src_ledger_transfer : Fn := { params := ["accounts", "amount"], body := [
    .ite (.or (.bin .le (.var "amount") (.lit (.num (F64.ofInt (0))))) (.bin .gt (.var "amount") (.field (.var "accounts") "from"))) [.ret (.lit .null)] [],
    .ret (.record [("from", .bin .sub (.field (.var "accounts") "from") (.var "amount")), ("to", .bin .add (.field (.var "accounts") "to") (.var "amount"))])] }

def src_ledger_sumAmounts_loop0 : List Stmt := [.set "total" (.bin .add (.var "total") (.var "amount"))]

def src_ledger_sumAmounts : Fn := { params := ["amounts"], body := [
    .set "total" (.lit (.num (F64.ofInt (0)))),
    .forOf "amount" (.var "amounts") src_ledger_sumAmounts_loop0,
    .ret (.var "total")] }

def src_phases_getActiveSpendingPhase_loop0 : List Stmt := [.ite (.or (.isNullish (.field (.var "phase") "fromAge")) (.bin .le (.field (.var "phase") "fromAge") (.var "age"))) [.set "active" (.var "phase")] [.brk]]

def src_phases_getActiveSpendingPhase : Fn := { params := ["resolvedPhases", "age"], body := [
    .set "active" (.index (.var "resolvedPhases") (.lit (.num (F64.ofInt (0))))),
    .forOf "phase" (.var "resolvedPhases") src_phases_getActiveSpendingPhase_loop0,
    .ret (.var "active")] }

def src_config_price_deriveAuctionPricing : Fn := { params := ["rawFloorPriceX96"], body := [
    .set "tickSpacing" (.call "src_config_price_deriveAuctionTickSpacing" [.var "rawFloorPriceX96"]),
    .ret (.record [("floorPriceX96", .bin .sub (.var "rawFloorPriceX96") (.bin .rem (.var "rawFloorPriceX96") (.var "tickSpacing"))), ("tickSpacing", .var "tickSpacing")])] }

def src_prelude_jsMap : Fn := { params := ["xs", "f"], body := [
    .set "out" (.array []),
    .ret (.call "src_prelude_mapFrom" [.var "xs", .var "f", .lit (.num (F64.ofInt (0))), .length (.var "xs"), .var "out"])] }

def src_features_mapGrows_lambda0 : Fn := { params := ["__env", "x"], body := [
    .push (.field (.field (.var "__env") "__up") "xs") (.var "x"),
    .ret (.var "x")] }

def src_features_mapShrinks_lambda1 : Fn := { params := ["__env", "x"], body := [
    .pop (.field (.field (.var "__env") "__up") "xs"),
    .ret (.var "x")] }

def Base_f : Fn := { params := ["this"], body := [
    .ret (.lit (.num (F64.ofInt (1))))] }

def Base_g : Fn := { params := ["this"], body := [
    .ret (.bin .add (.callM (.var "this") "f" []) (.lit (.num (F64.ofInt (1)))))] }

def Sub_f : Fn := { params := ["this"], body := [
    .ret (.lit (.num (F64.ofInt (10))))] }

def src_features_counterTwice_lambda2 : Fn := { params := ["__env"], body := [
    .setField (.field (.var "__env") "__up") "n" (.bin .add (.field (.field (.var "__env") "__up") "n") (.lit (.num (F64.ofInt (1))))),
    .ret (.field (.field (.var "__env") "__up") "n")] }

def src_features_loopCaptures_lambda3 : Fn := { params := ["__env"], body := [
    .ret (.bin .mul (.field (.var "__env") "x") (.lit (.num (F64.ofInt (2)))))] }

def src_features_scaled_lambda4 : Fn := { params := ["__env", "x"], body := [
    .ret (.bin .mul (.var "x") (.field (.field (.var "__env") "__up") "k"))] }

def src_features_indexed_lambda5 : Fn := { params := ["__env", "x", "i"], body := [
    .ret (.bin .add (.var "x") (.var "i"))] }

def src_prelude_jsFilter : Fn := { params := ["xs", "f"], body := [
    .set "out" (.array []),
    .ret (.call "src_prelude_filterFrom" [.var "xs", .var "f", .lit (.num (F64.ofInt (0))), .length (.var "xs"), .var "out"])] }

def src_features_positives_lambda6 : Fn := { params := ["__env", "x"], body := [
    .ret (.bin .gt (.var "x") (.lit (.num (F64.ofInt (0)))))] }

def src_prelude_jsReduce : Fn := { params := ["xs", "f", "init"], body := [
    .ret (.call "src_prelude_reduceFrom" [.var "xs", .var "f", .lit (.num (F64.ofInt (0))), .length (.var "xs"), .var "init"])] }

def src_features_total_lambda7 : Fn := { params := ["__env", "acc", "x"], body := [
    .ret (.bin .add (.var "acc") (.var "x"))] }

def src_prelude_jsSome : Fn := { params := ["xs", "f"], body := [
    .ret (.call "src_prelude_someFrom" [.var "xs", .var "f", .lit (.num (F64.ofInt (0))), .length (.var "xs")])] }

def src_features_anyOver_lambda8 : Fn := { params := ["__env", "x"], body := [
    .ret (.bin .gt (.var "x") (.field (.field (.var "__env") "__up") "limit"))] }

def src_features_sumAll_loop0 : List Stmt := [.set "t" (.bin .add (.var "t") (.var "x"))]

def src_features_sumAll : Fn := { params := ["xs"], body := [
    .set "t" (.lit (.num (F64.ofInt (0)))),
    .forOf "x" (.var "xs") src_features_sumAll_loop0,
    .ret (.var "t")] }

def Shape_area : Fn := { params := ["this"], body := [
    .ret (.bin .mul (.field (.var "this") "size") (.field (.var "this") "size"))] }

def Shape_describe : Fn := { params := ["this"], body := [
    .ret (.bin .add (.callM (.var "this") "area" []) (.lit (.num (F64.ofInt (1)))))] }

def Shape___init : Fn := { params := ["this", "size"], body := [
    .setField (.var "this") "size" (.var "size")] }

def Doubled_area : Fn := { params := ["this"], body := [
    .ret (.bin .add (.call "Shape.area" [.var "this"]) (.lit (.num (F64.ofInt (100)))))] }

def Doubled___init : Fn := { params := ["this", "size"], body := [
    .expr (.call "Shape.__init" [.var "this", .bin .mul (.var "size") (.lit (.num (F64.ofInt (2))))])] }

def src_config_price_deriveAuctionTickSpacing : Fn := { params := ["floorPriceX96"], body := [
    .set "tickSpacing" (.bin .div (.var "floorPriceX96") (.lit (.big 100))),
    .ret (.cond (.bin .gt (.var "tickSpacing") (.lit (.big 0))) (.var "tickSpacing") (.lit (.big 1)))] }

def src_prelude_mapFrom : Fn := { params := ["xs", "f", "i", "n", "out"], body := [
    .ite (.bin .eq (.var "i") (.var "n")) [.ret (.var "out")] [],
    .ite (.bin .ge (.var "i") (.length (.var "xs"))) [.expr (.call "__stuck" [])] [],
    .push (.var "out") (.callV (.var "f") [.index (.var "xs") (.var "i"), .var "i", .var "xs"]),
    .ret (.call "src_prelude_mapFrom" [.var "xs", .var "f", .bin .add (.var "i") (.lit (.num (F64.ofInt (1)))), .var "n", .var "out"])] }

def src_prelude_filterFrom : Fn := { params := ["xs", "f", "i", "n", "out"], body := [
    .ite (.bin .eq (.var "i") (.var "n")) [.ret (.var "out")] [],
    .ite (.bin .ge (.var "i") (.length (.var "xs"))) [.expr (.call "__stuck" [])] [],
    .set "x" (.index (.var "xs") (.var "i")),
    .ite (.callV (.var "f") [.var "x", .var "i", .var "xs"]) [.push (.var "out") (.var "x")] [],
    .ret (.call "src_prelude_filterFrom" [.var "xs", .var "f", .bin .add (.var "i") (.lit (.num (F64.ofInt (1)))), .var "n", .var "out"])] }

def src_prelude_reduceFrom : Fn := { params := ["xs", "f", "i", "n", "acc"], body := [
    .ite (.bin .eq (.var "i") (.var "n")) [.ret (.var "acc")] [],
    .ite (.bin .ge (.var "i") (.length (.var "xs"))) [.expr (.call "__stuck" [])] [],
    .ret (.call "src_prelude_reduceFrom" [.var "xs", .var "f", .bin .add (.var "i") (.lit (.num (F64.ofInt (1)))), .var "n", .callV (.var "f") [.var "acc", .index (.var "xs") (.var "i"), .var "i", .var "xs"]])] }

def src_prelude_someFrom : Fn := { params := ["xs", "f", "i", "n"], body := [
    .ite (.bin .eq (.var "i") (.var "n")) [.ret (.lit (.bool false))] [],
    .ite (.bin .ge (.var "i") (.length (.var "xs"))) [.expr (.call "__stuck" [])] [],
    .ite (.callV (.var "f") [.index (.var "xs") (.var "i"), .var "i", .var "xs"]) [.ret (.lit (.bool true))] [],
    .ret (.call "src_prelude_someFrom" [.var "xs", .var "f", .bin .add (.var "i") (.lit (.num (F64.ofInt (1)))), .var "n"])] }

def Base_new : Fn := { params := ["a", "b"], body := [
    .set "this" (.record [("__class", .lit (.str [66, 97, 115, 101]))]),
    .ret (.var "this")] }

def Sub_new : Fn := { params := ["a", "b"], body := [
    .set "this" (.record [("__class", .lit (.str [83, 117, 98]))]),
    .ret (.var "this")] }

def Shape_new : Fn := { params := ["size"], body := [
    .set "this" (.record [("__class", .lit (.str [83, 104, 97, 112, 101]))]),
    .expr (.call "Shape.__init" [.var "this", .var "size"]),
    .ret (.var "this")] }

def Doubled_new : Fn := { params := ["size"], body := [
    .set "this" (.record [("__class", .lit (.str [68, 111, 117, 98, 108, 101, 100]))]),
    .expr (.call "Doubled.__init" [.var "this", .var "size"]),
    .ret (.var "this")] }

def prog : Prog := fun name => match name with
  | "src_features_amountOf" => some src_features_amountOf
  | "src_features_mapGrows" => some src_features_mapGrows
  | "src_features_mapShrinks" => some src_features_mapShrinks
  | "src_features_clamp01" => some src_features_clamp01
  | "src_features_overrideSeen" => some src_features_overrideSeen
  | "src_features_counterTwice" => some src_features_counterTwice
  | "src_features_loopCaptures" => some src_features_loopCaptures
  | "src_features_scaled" => some src_features_scaled
  | "src_features_indexed" => some src_features_indexed
  | "src_features_positives" => some src_features_positives
  | "src_features_total" => some src_features_total
  | "src_features_anyOver" => some src_features_anyOver
  | "src_features_firstNegative" => some src_features_firstNegative
  | "src_features_positivesLoop" => some src_features_positivesLoop
  | "src_features_sumPlusOne" => some src_features_sumPlusOne
  | "src_features_dispatch" => some src_features_dispatch
  | "src_features_growBoth" => some src_features_growBoth
  | "src_features_treeSum" => some src_features_treeSum
  | "src_async_withdrawStale" => some src_async_withdrawStale
  | "src_async_withdrawSafe" => some src_async_withdrawSafe
  | "src_async_twoWaits" => some src_async_twoWaits
  | "src_ledger_transfer" => some src_ledger_transfer
  | "src_ledger_sumAmounts" => some src_ledger_sumAmounts
  | "src_phases_getActiveSpendingPhase" => some src_phases_getActiveSpendingPhase
  | "src_config_price_deriveAuctionPricing" => some src_config_price_deriveAuctionPricing
  | "src_prelude_jsMap" => some src_prelude_jsMap
  | "src_features_mapGrows_lambda0" => some src_features_mapGrows_lambda0
  | "src_features_mapShrinks_lambda1" => some src_features_mapShrinks_lambda1
  | "Base_f" => some Base_f
  | "Base_g" => some Base_g
  | "Sub_f" => some Sub_f
  | "src_features_counterTwice_lambda2" => some src_features_counterTwice_lambda2
  | "src_features_loopCaptures_lambda3" => some src_features_loopCaptures_lambda3
  | "src_features_scaled_lambda4" => some src_features_scaled_lambda4
  | "src_features_indexed_lambda5" => some src_features_indexed_lambda5
  | "src_prelude_jsFilter" => some src_prelude_jsFilter
  | "src_features_positives_lambda6" => some src_features_positives_lambda6
  | "src_prelude_jsReduce" => some src_prelude_jsReduce
  | "src_features_total_lambda7" => some src_features_total_lambda7
  | "src_prelude_jsSome" => some src_prelude_jsSome
  | "src_features_anyOver_lambda8" => some src_features_anyOver_lambda8
  | "src_features_sumAll" => some src_features_sumAll
  | "Shape_area" => some Shape_area
  | "Shape_describe" => some Shape_describe
  | "Shape___init" => some Shape___init
  | "Doubled_area" => some Doubled_area
  | "Doubled___init" => some Doubled___init
  | "src_config_price_deriveAuctionTickSpacing" => some src_config_price_deriveAuctionTickSpacing
  | "src_prelude_mapFrom" => some src_prelude_mapFrom
  | "src_prelude_filterFrom" => some src_prelude_filterFrom
  | "src_prelude_reduceFrom" => some src_prelude_reduceFrom
  | "src_prelude_someFrom" => some src_prelude_someFrom
  | "Base.f" => some Base_f
  | "Base.g" => some Base_g
  | "Base.__new" => some Base_new
  | "Sub.f" => some Sub_f
  | "Sub.g" => some Base_g
  | "Sub.__new" => some Sub_new
  | "Shape.area" => some Shape_area
  | "Shape.describe" => some Shape_describe
  | "Shape.__init" => some Shape___init
  | "Shape.__new" => some Shape_new
  | "Doubled.area" => some Doubled_area
  | "Doubled.describe" => some Shape_describe
  | "Doubled.__init" => some Doubled___init
  | "Doubled.__new" => some Doubled_new
  | _ => none

end Gen
