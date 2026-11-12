import Spike.WP
open Core Gen

attribute [simp] Gen.prog Gen.src_features_amountOf Gen.src_features_clamp01

abbrev numV (x : Int) : Val := .num (F64.ofInt x)

/-! ## `unknown`: no type mapping, only what the code tests -/

set_option maxRecDepth 20000 in
theorem amountOf_spec (v : Val) (h : Heap) :
    (match run 30 prog src_features_amountOf [v] h with | .ok r _ => some r | _ => none) =
      some (match v with
        | .num x => .num x
        | .str s => numV s.length
        | _ => numV 0) := by
  cases v <;> simp [run, execList, exec, eval, binary, typeName, Env.put, truthy]

/-! ## `NaN`: fractions are fine when a proof needs no rounding argument -/

theorem le_of_not_lt {x y : F64} (hx : x ≠ .nan) (hy : y ≠ .nan) (h : x.lt y = false) : y.le x = true := by
  cases x with
  | nan => exact absurd rfl hx
  | inf a =>
    cases y with
    | nan => exact absurd rfl hy
    | inf b => cases a <;> cases b <;> simp_all [F64.lt, F64.le, F64.le.eq']
    | fin b m => cases a <;> simp_all [F64.lt, F64.le, F64.le.eq']
  | fin a n =>
    cases y with
    | nan => exact absurd rfl hy
    | inf b => cases b <;> simp_all [F64.lt, F64.le, F64.le.eq']
    | fin b m =>
      simp only [F64.lt, decide_eq_false_iff_not] at h
      simp only [F64.le, F64.lt, F64.le.eq']
      generalize F64.signed a n = p at *
      generalize F64.signed b m = q at *
      by_cases hq : q < p
      · simp [hq]
      · have : q = p := by omega
        simp [this]

/-- For every double except `NaN`, the result is between 0 and 1. -/
theorem clamp01_range (x : F64) (hx : x ≠ .nan) (h : Heap) :
    WpRun prog src_features_clamp01 [.num x] h fun v _ =>
      ∃ r, v = .num r ∧ (F64.ofInt 0).le r = true ∧ r.le (F64.ofInt 1) = true := by
  apply wprun
  simp only [src_features_clamp01]
  by_cases hlo : x.lt (F64.ofInt 0) = true
  · core_run
  · by_cases hhi : (F64.ofInt 1).lt x = true
    · core_run
    · have n0 : F64.ofInt 0 ≠ .nan := by simp [F64.ofInt]
      have n1 : F64.ofInt 1 ≠ .nan := by simp [F64.ofInt]
      have h1 := le_of_not_lt hx n0 (by simpa using hlo)
      have h2 := le_of_not_lt n1 hx (by simpa using hhi)
      core_run

/-- `NaN` compares false both ways, so it walks straight through a clamp. -/
example : (match run 30 prog src_features_clamp01 [.num .nan] [] with
    | .ok (.num .nan) _ => true | _ => false) = true := by decide +kernel

/-! ## Every order of `async` turns -/

attribute [simp] Gen.src_async_withdrawStale_segs Gen.src_async_withdrawSafe_segs

abbrev JsTask := List (List Stmt) × Env

/-- Runs two tasks in a given order of turns: this is what real I/O can do. -/
def runOrder : List Bool → JsTask → JsTask → Heap → Option Heap
  | [], _, _, h => some h
  | true :: o, (seg :: m, e), b, h => match execList 30 prog ⟨e, h⟩ seg with
    | .ok .normal s => runOrder o (m, s.env) b s.heap
    | _ => none
  | false :: o, a, (seg :: m, e), h => match execList 30 prog ⟨e, h⟩ seg with
    | .ok .normal s => runOrder o a (m, s.env) s.heap
    | _ => none
  | _, _, _, _ => none

def env2 (x : Int) : Env := (Env.put (fun _ => none) "a" (.ref 0)).put "amount" (numV x)

def acct (b : Int) : Obj := .record [("balance", numV b), ("log", .ref 1)]

def balanceAfter (r : Option Heap) : Option Val := r.bind fun h => readField h (.ref 0) "balance"

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- The safe version keeps both withdrawals in all six orders of turns. -/
theorem safe_every_order (b x y : Int)
    (h1 : -9007199254740991 ≤ b - x) (h2 : b - x ≤ 9007199254740991)
    (h3 : -9007199254740991 ≤ b - y) (h4 : b - y ≤ 9007199254740991)
    (h5 : -9007199254740991 ≤ b - x - y) (h6 : b - x - y ≤ 9007199254740991)
    (o : List Bool) (ho : o ∈ [[true, true, false, false], [true, false, true, false], [true, false, false, true],
      [false, true, true, false], [false, true, false, true], [false, false, true, true]]) :
    balanceAfter (runOrder o (src_async_withdrawSafe_segs, env2 x) (src_async_withdrawSafe_segs, env2 y)
      [acct b, .array []]) = some (numV (b - x - y)) := by
  have h7 : -9007199254740991 ≤ b - y - x := by omega
  have h8 : b - y - x ≤ 9007199254740991 := by omega
  have comm : b - y - x = b - x - y := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega) [runOrder, balanceAfter, acct, env2, execList, exec, eval, evalList, binary, readField,
      Env.put, List.lookup, List.filter, comm]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- The stale version depends on the order: one way nothing is lost, the other way the first is. -/
theorem stale_depends_on_order (b x y : Int)
    (h1 : -9007199254740991 ≤ b - x) (h2 : b - x ≤ 9007199254740991)
    (h3 : -9007199254740991 ≤ b - y) (h4 : b - y ≤ 9007199254740991)
    (h5 : -9007199254740991 ≤ b - x - y) (h6 : b - x - y ≤ 9007199254740991) :
    balanceAfter (runOrder [true, true, false, false] (src_async_withdrawStale_segs, env2 x)
        (src_async_withdrawStale_segs, env2 y) [acct b, .array []]) = some (numV (b - x - y)) ∧
    balanceAfter (runOrder [true, false, true, false] (src_async_withdrawStale_segs, env2 x)
        (src_async_withdrawStale_segs, env2 y) [acct b, .array []]) = some (numV (b - y)) := by
  simp (disch := omega) [runOrder, balanceAfter, acct, env2, execList, exec, eval, evalList, binary, readField,
    Env.put, List.lookup, List.filter]

#print axioms amountOf_spec
#print axioms clamp01_range
#print axioms safe_every_order
#print axioms stale_depends_on_order
