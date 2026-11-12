import Core

/-! # `async` on top of Core

Core (`Core.lean`) is untouched: this file adds a layer above it, so the synchronous model and
every proof about it stay exactly as they were. An `async` function is a list of `AStmt`: plain Core
statements, and the few forms that can wait or reject. They run against an *oracle*, which answers
each outside call from the call and everything that happened before it, and a *history* of calls.

What each form means (the same thing the Lean view in `ProofciAsync.lean` says):

* `await x op args`: evaluate `args`, ask the oracle, append the call and its answer to the history.
  A value is stored in `x`. A rejection is thrown, as an `Error` object `{name, message}`.
* `tryCatch`, `tryFinally`: as in JavaScript, for rejections and `throw`. Leaving the model (`stuck`:
  fuel, or a shape the model doesn't cover) is not an exception and is never caught.
* `throw e`: rejects with the value of `e`.

An `await` always takes one step and nothing else runs in between: that is the sequential reading,
and it is only right for functions the hazard rule (`typescript/hazard.mjs`) accepts. This layer is
executable and is tested against Node (`asynccore.mjs`); there is no bridge theorem to it yet. -/

namespace Core.Async

open Core

instance : Inhabited Val := ⟨.undef⟩

/-- A value with its objects spelled out, so that it can be built on any heap and read back. -/
inductive Data where
  | leaf (v : Val)
  | obj (fields : List (String × Data))
  | arr (items : List Data)
  deriving Inhabited

/-- How the world answered one call. -/
inductive Ans where
  | value (d : Data)
  | reject (nm msg : List Nat)
  deriving Inhabited

structure Event where
  op : String
  args : List Data
  ans : Ans

/-- The world: an answer for each call, given everything asked before it. -/
abbrev Oracle := String → List Data → List Event → Ans

inductive AStmt where
  | stmt (c : Stmt)
  | await (x : String) (op : String) (args : List Expr)
  | awaitFn (x : String) (f : String) (args : List Expr)
  | ite (c : Expr) (t e : List AStmt)
  | forOf (x : String) (e : Expr) (body : List AStmt)
  | whileL (c : Expr) (body step : List AStmt)
  | tryCatch (body : List AStmt) (x : String) (handler : List AStmt)
  | tryFinally (body fin : List AStmt)
  | throw (e : Expr)
  | ret (e : Expr)
  | brk
  | cont

structure AFn where
  params : List String
  body : List AStmt

abbrev AProg := String → Option AFn

structure AS where
  st : St
  hist : List Event

inductive AOut where
  | ok (c : Cmp) (s : AS)
  | thrown (v : Val) (s : AS)
  | stuck

/-- Builds `d` on the heap, children first, as a record or array literal would be. -/
partial def alloc (h : Heap) : Data → Val × Heap
  | .leaf v => (v, h)
  | .obj fs =>
    let (vs, h') := fs.foldl (fun (acc : List (String × Val) × Heap) (k, d) =>
      let (v, h2) := alloc acc.2 d
      (acc.1 ++ [(k, v)], h2)) ([], h)
    (.ref h'.length, h' ++ [.record vs])
  | .arr ds =>
    let (vs, h') := ds.foldl (fun (acc : List Val × Heap) d =>
      let (v, h2) := alloc acc.2 d
      (acc.1 ++ [v], h2)) ([], h)
    (.ref h'.length, h' ++ [.array vs])

/-- Reads a value back as data. A cycle gets cut off at the fuel. -/
def readData : Nat → Heap → Val → Data
  | 0, _, v => .leaf v
  | f + 1, h, .ref l => match h[l]? with
    | some (.array xs) => .arr (xs.attach.map fun x => readData f h x.1)
    | some (.record fs) => .obj (fs.attach.map fun x => (x.1.1, readData f h x.1.2))
    | none => .leaf .undef
  | _ + 1, _, v => .leaf v

def rejection (h : Heap) (nm msg : List Nat) : Val × Heap :=
  alloc h (.obj [("name", .leaf (.str nm)), ("message", .leaf (.str msg))])

mutual

def aexec : Nat → Prog → AProg → Oracle → AS → AStmt → AOut
  | 0, _, _, _, _, _ => .stuck
  | f + 1, p, a, o, s, c => match c with
    | .stmt c => match exec f p s.st c with
      | .ok r st => .ok r ⟨st, s.hist⟩
      | .thrown v st => .thrown v ⟨st, s.hist⟩
      | .stuck => .stuck
    | .await x op args => match evalList f p s.st args with
      | .ok vs st =>
        let ds := vs.map (readData 50 st.heap)
        match o op ds s.hist with
        | .value d =>
          let (v, h) := alloc st.heap d
          let env := if x == "" then st.env else st.env.put x v
          .ok .normal ⟨{ st with env, heap := h }, s.hist ++ [⟨op, ds, .value d⟩]⟩
        | .reject n m =>
          let (e, h) := rejection st.heap n m
          .thrown e ⟨{ st with heap := h }, s.hist ++ [⟨op, ds, .reject n m⟩]⟩
      | .thrown v st => .thrown v ⟨st, s.hist⟩
      | .stuck => .stuck
    | .awaitFn x g args => match evalList f p s.st args with
      | .ok vs st => match a g with
        | some fn => match arun f p a o fn vs ⟨st, s.hist⟩ with
          | .ok (.ret v) r =>
            let env := if x == "" then st.env else st.env.put x v
            .ok .normal ⟨{ st with env, heap := r.st.heap }, r.hist⟩
          | .ok _ _ => .stuck
          | .thrown v r => .thrown v ⟨{ st with heap := r.st.heap }, r.hist⟩
          | .stuck => .stuck
        | none => .stuck
      | .thrown v st => .thrown v ⟨st, s.hist⟩
      | .stuck => .stuck
    | .ite c t e => match eval f p s.st c with
      | .ok v st => aexecList f p a o ⟨st, s.hist⟩ (if truthy v then t else e)
      | .thrown v st => .thrown v ⟨st, s.hist⟩
      | .stuck => .stuck
    | .forOf x e body => match eval f p s.st e with
      | .ok v st => aiterate f p a o x v 0 body ⟨st, s.hist⟩
      | .thrown v st => .thrown v ⟨st, s.hist⟩
      | .stuck => .stuck
    | .whileL c body step => awhile f p a o c body step s
    | .tryCatch body x h => match aexecList f p a o s body with
      | .thrown v r => aexecList f p a o ⟨{ r.st with env := r.st.env.put x v }, r.hist⟩ h
      | other => other
    | .tryFinally body fin => match aexecList f p a o s body with
      | .ok r s' => match aexecList f p a o s' fin with
        | .ok .normal s'' => .ok r s''
        | other => other
      | .thrown v s' => match aexecList f p a o s' fin with
        | .ok .normal s'' => .thrown v s''
        | other => other
      | .stuck => .stuck
    | .throw e => match eval f p s.st e with
      | .ok v st => .thrown v ⟨st, s.hist⟩
      | .thrown v st => .thrown v ⟨st, s.hist⟩
      | .stuck => .stuck
    | .ret e => match eval f p s.st e with
      | .ok v st => .ok (.ret v) ⟨st, s.hist⟩
      | .thrown v st => .thrown v ⟨st, s.hist⟩
      | .stuck => .stuck
    | .brk => .ok .brk s
    | .cont => .ok .cont s

def aexecList : Nat → Prog → AProg → Oracle → AS → List AStmt → AOut
  | 0, _, _, _, _, _ => .stuck
  | _ + 1, _, _, _, s, [] => .ok .normal s
  | f + 1, p, a, o, s, c :: cs => match aexec f p a o s c with
    | .ok .normal s' => aexecList f p a o s' cs
    | other => other

def aiterate : Nat → Prog → AProg → Oracle → String → Val → Nat → List AStmt → AS → AOut
  | 0, _, _, _, _, _, _, _, _ => .stuck
  | f + 1, p, a, o, x, v, i, body, s => match v with
    | .ref l => match s.st.heap[l]? with
      | some (.array xs) => match xs[i]? with
        | none => .ok .normal s
        | some item => match aexecList f p a o ⟨{ s.st with env := s.st.env.put x item }, s.hist⟩ body with
          | .ok .normal s' => aiterate f p a o x v (i + 1) body s'
          | .ok .cont s' => aiterate f p a o x v (i + 1) body s'
          | .ok .brk s' => .ok .normal s'
          | other => other
      | _ => .thrown typeError s
    | _ => .thrown typeError s

def awhile : Nat → Prog → AProg → Oracle → Expr → List AStmt → List AStmt → AS → AOut
  | 0, _, _, _, _, _, _, _ => .stuck
  | f + 1, p, a, o, c, body, step, s => match eval f p s.st c with
    | .ok v st =>
      if truthy v then
        let again := fun s₂ => match aexecList f p a o s₂ step with
          | .ok .normal s₃ => awhile f p a o c body step s₃
          | other => other
        match aexecList f p a o ⟨st, s.hist⟩ body with
        | .ok .normal s₂ => again s₂
        | .ok .cont s₂ => again s₂
        | .ok .brk s₂ => .ok .normal s₂
        | other => other
      else .ok .normal ⟨st, s.hist⟩
    | .thrown v st => .thrown v ⟨st, s.hist⟩
    | .stuck => .stuck

/-- Calls an async function: its body runs to its first `return`, or off the end. -/
def arun : Nat → Prog → AProg → Oracle → AFn → List Val → AS → AOut
  | 0, _, _, _, _, _, _ => .stuck
  | f + 1, p, a, o, fn, args, s =>
    let env : Env := (fn.params.zip args).foldl (fun e (x, v) => e.put x v) (fun _ => none)
    let env := fn.params.foldl (fun e x => if (e x).isSome then e else e.put x .undef) env
    match aexecList f p a o ⟨{ env, heap := s.st.heap }, s.hist⟩ fn.body with
    | .ok (.ret v) r => .ok (.ret v) r
    | .ok _ r => .ok (.ret .undef) r
    | other => other

end

/-! ## Running a case, and the text form compared with Node -/

def showVal : Nat → Heap → Val → String
  | 0, _, _ => "?"
  | _ + 1, _, .undef => "undefined"
  | _ + 1, _, .null => "null"
  | _ + 1, _, .bool b => toString b
  | _ + 1, _, .fn _ _ => "fn"
  | _ + 1, _, .num x => if x == .nan then "NaN" else s!"#{x.toBits}"
  | _ + 1, _, .big n => s!"{n}n"
  | _ + 1, _, .str s => "s[" ++ ",".intercalate (s.map toString) ++ "]"
  | f + 1, h, .ref l => match h[l]? with
    | some (.array xs) => "[" ++ ",".intercalate (xs.attach.map fun x => showVal f h x.1) ++ "]"
    | some (.record fs) =>
      let sorted := ((fs.filter (·.1 != "__class")).toArray.qsort (fun a b => a.1 < b.1)).toList
      "{" ++ ",".intercalate (sorted.map fun (k, v) => k ++ ":" ++ showVal f h v) ++ "}"
    | none => "?"

def showData (d : Data) : String :=
  let (v, h) := alloc [] d
  showVal 50 h v

def showEvent (e : Event) : String :=
  e.op ++ "(" ++ ",".intercalate (e.args.map showData) ++ ")" ++ match e.ans with
    | .value d => "->v:" ++ showData d
    | .reject _ m => "->r:s[" ++ ",".intercalate (m.map toString) ++ "]"

/-- A scripted world: the nth call must be the nth entry, and gets its answer. A call the script
doesn't expect is rejected, so a model that asks something else disagrees with Node. -/
def scripted (script : List (String × Ans)) : Oracle := fun op _ hist =>
  match script[hist.length]? with
  | some (op', ans) => if op' == op then ans else .reject [69, 114, 114, 111, 114] (("unexpected " ++ op).toList.map Char.toNat)
  | none => .reject [69, 114, 114, 111, 114] ("no more answers".toList.map Char.toNat)

/-- One case: the result or the rejection, and the trace of outside calls. -/
def report (p : Prog) (a : AProg) (o : Oracle) (fn : AFn) (args : List Data) : String :=
  let (vs, h) := args.foldl (fun (acc : List Val × Heap) d =>
    let (v, h') := alloc acc.2 d
    (acc.1 ++ [v], h')) ([], [])
  let trace (s : AS) := "|" ++ ";".intercalate (s.hist.map showEvent)
  match arun 5000 p a o fn vs ⟨⟨fun _ => none, h⟩, []⟩ with
  | .ok (.ret v) s => "ASYNC fulfilled " ++ showVal 50 s.st.heap v ++ trace s
  | .ok _ s => "ASYNC fulfilled undefined" ++ trace s
  | .thrown v s => "ASYNC rejected " ++ showVal 50 s.st.heap v ++ trace s
  | .stuck => "ASYNC stuck"

end Core.Async
