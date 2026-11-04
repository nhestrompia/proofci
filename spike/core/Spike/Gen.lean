import Core
open Core
set_option maxRecDepth 4000
namespace Gen

def src_heldout_rangePosition : Fn := { params := ["cell", "start", "end"], body := [
    .ite (.or (.bin .lt (.var "cell") (.var "start")) (.bin .gt (.var "cell") (.var "end"))) [.ret (.lit .null)] [],
    .ite (.bin .eq (.var "cell") (.var "start")) [.ret (.lit (.str [115, 116, 97, 114, 116]))] [],
    .ite (.bin .eq (.var "cell") (.var "end")) [.ret (.lit (.str [101, 110, 100]))] [],
    .ret (.lit (.str [109, 105, 100, 100, 108, 101]))] }

def prog : Prog := fun name => match name with
  | "src_heldout_rangePosition" => some src_heldout_rangePosition
  | _ => none

end Gen
