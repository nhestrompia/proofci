import Spike.WP
open Core Gen

/-! A race, proved. `drain` runs jobs in their real order, so the outcome of two
overlapping calls is a theorem about every starting balance. -/

attribute [simp] Gen.src_async_withdrawStale_segs Gen.src_async_withdrawSafe_segs

def acct (b : Int) (log : Loc) : Obj :=
  .record [("balance", .num (F64.ofInt b)), ("log", .ref log)]

/-- One `Promise.all` of two calls on one account, run to the end. -/
def twice (segs : List (List Stmt)) (x y : Int) (h : Heap) (f : Nat) :=
  drain f prog (startAll [(segs, ["a", "amount"], [.ref 0, .num (F64.ofInt x)]),
    (segs, ["a", "amount"], [.ref 0, .num (F64.ofInt y)])]) h

/-- Balance after the run. -/
def finalBalance (r : Out Unit) : Option Val := match r with
  | .ok _ s => readField s.heap (.ref 0) "balance"
  | _ => none

/-- Both calls read before either writes, so the first withdrawal disappears. -/
example : finalBalance (twice src_async_withdrawStale_segs 10 20 [acct 100 1, .array []] 500)
    = some (.num (F64.ofInt 80)) := by decide +kernel

/-- Reading and writing in one turn keeps both withdrawals. -/
example : finalBalance (twice src_async_withdrawSafe_segs 10 20 [acct 100 1, .array []] 500)
    = some (.num (F64.ofInt 70)) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- For every balance and amounts: the stale version keeps only the second withdrawal. -/
theorem stale_loses_first (b x y : Int)
    (h1 : -9007199254740991 ≤ b - x) (h2 : b - x ≤ 9007199254740991)
    (h3 : -9007199254740991 ≤ b - y) (h4 : b - y ≤ 9007199254740991) :
    finalBalance (twice src_async_withdrawStale_segs x y [acct b 1, .array []] 40)
      = some (.num (F64.ofInt (b - y))) := by
  simp (disch := omega) [twice, finalBalance, acct, startAll, drain, execList, exec, eval, evalList, binary, readField,
    Env.put, List.lookup, List.filter]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- For every balance and amounts: the safe version keeps both withdrawals. -/
theorem safe_keeps_both (b x y : Int)
    (h1 : -9007199254740991 ≤ b - x) (h2 : b - x ≤ 9007199254740991)
    (h3 : -9007199254740991 ≤ b - x - y) (h4 : b - x - y ≤ 9007199254740991) :
    finalBalance (twice src_async_withdrawSafe_segs x y [acct b 1, .array []] 40)
      = some (.num (F64.ofInt (b - x - y))) := by
  simp (disch := omega) [twice, finalBalance, acct, startAll, drain, execList, exec, eval, evalList, binary, readField,
    Env.put, List.lookup, List.filter]

#print axioms stale_loses_first
#print axioms safe_keeps_both
