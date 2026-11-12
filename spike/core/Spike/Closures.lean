import Spike.WP
open Core Gen

attribute [simp] Gen.src_features_counterTwice Gen.prog Gen.src_features_counterTwice_lambda0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- A closure shares `n` with its function: the third call sees the `+ 10` from outside. -/
theorem counter_shares_state (n : Int) (h : Heap)
    (b1 : -9007199254740991 ≤ n + 1) (b2 : n + 1 ≤ 9007199254740991)
    (b3 : -9007199254740991 ≤ n + 1 + 1) (b4 : n + 1 + 1 ≤ 9007199254740991)
    (b5 : -9007199254740991 ≤ n + 1 + 1 + 10) (b6 : n + 1 + 1 + 10 ≤ 9007199254740991)
    (b7 : -9007199254740991 ≤ n + 1 + 1 + 10 + 1) (b8 : n + 1 + 1 + 10 + 1 ≤ 9007199254740991) :
    (match run 40 prog src_features_counterTwice [.num (F64.ofInt n)] h with
      | .ok (.ref l) s => s.heap[l]?
      | _ => none)
    = some (.array [.num (F64.ofInt (n + 1)), .num (F64.ofInt (n + 1 + 1)), .num (F64.ofInt (n + 1 + 1 + 10 + 1))]) := by
  simp (disch := omega) [run, execList, exec, eval, evalList, evalFields, binary, readField, Env.put, List.lookup,
    List.filter, List.getElem?_append, List.getElem?_set, List.length_append, List.length_set]

/-- The class of an object picks the method, even from code inherited from a parent. -/
example : (match run 60 prog src_features_overrideSeen [] [] with
    | .ok v _ => some v
    | _ => none) = some (.num (F64.ofInt 11)) := by decide +kernel
