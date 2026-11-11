import Aeneas
import ProofciJs

/-!
# `async` functions for translated TypeScript

An `async` function is a sequential computation over an *oracle* and a *history*. The oracle
answers every call to code ProofCI does not read (a database, the network, a package) and may
look at everything that happened before it, so `find` after `update` can differ from `find`
before it. `await` of such a call is one step: the call and its answer are appended to the
history. A guarantee proved for every oracle holds for every real run, because a real run
answers its n-th outside call with some value or some rejection, and some oracle does the same.
It also holds when other tasks change the world in between: their effect is only a different
answer. A proof leans on how the world behaves only through a hypothesis about the oracle, and
the contract states it.

What this does not model: other tasks changing *in-process* state (module variables, mutable
captured variables) between two steps. The translator refuses a function that reads such
state after an `await`, so the sequential reading is the only reading.

`Result` still means what it does elsewhere: `ok` is what JavaScript computes, and `fail` is
leaving the model. A rejected promise or a `throw` is not a failure: it is an outcome the
guarantee can talk about.

This file declares no axioms.
-/

open Aeneas Aeneas.Std Result

namespace Js

/-- A thrown `Error` object. Only errors are modelled as thrown values: the translator refuses
`throw` of anything else, and the policy's effect entries state that an outside call rejects
only with `Error` objects. -/
structure Exn where
  «name» : Str
  message : Str
  deriving DecidableEq, Repr

/-- How a promise settled. -/
inductive Settled (α : Type) where
  | fulfilled (a : α)
  | rejected (e : Exn)
  deriving DecidableEq

/-- The outside operations of a program: one per `effects:` entry. The argument is the
receiver (when the call has one, an opaque handle) together with the arguments. -/
structure World where
  Op : Type
  Arg : Op → Type
  Res : Op → Type

/-- How the outside world answered one call. -/
inductive Answer (α : Type) where
  | value (v : α)
  | reject (e : Exn)
  deriving DecidableEq

namespace World
variable (W : World)

/-- One call and its answer. -/
structure Event where
  op : W.Op
  arg : W.Arg op
  ans : Answer (W.Res op)

/-- Everything that has happened so far, oldest first. -/
abbrev Hist := List W.Event

/-- The world: an answer to each call, given everything that happened before it. -/
abbrev Oracle := (op : W.Op) → W.Arg op → W.Hist → Answer (W.Res op)

end World

/-- A computation that may call the outside world, wait, and reject. -/
def Eff (W : World) (α : Type) : Type := W.Oracle → W.Hist → Result (Settled α × W.Hist)

namespace Eff
variable {W : World} {α β : Type}

protected def pure (a : α) : Eff W α := fun _ h => ok (.fulfilled a, h)

protected def bind (m : Eff W α) (f : α → Eff W β) : Eff W β := fun o h => do
  let (r, h') ← m o h
  match r with
  | .fulfilled a => f a o h'
  | .rejected e => ok (.rejected e, h')

instance : Monad (Eff W) where
  pure := Eff.pure
  bind := Eff.bind

/-- Code that never waits: its `Result` is the whole story. -/
instance : MonadLift Result (Eff W) := ⟨fun m _ h => do let a ← m; ok (.fulfilled a, h)⟩

/-- `await f(args)`, for an outside operation `op`: one step, recorded in the history. -/
def call (op : W.Op) (arg : W.Arg op) : Eff W (W.Res op) := fun o h =>
  match o op arg h with
  | .value v => ok (.fulfilled v, h ++ [⟨op, arg, .value v⟩])
  | .reject e => ok (.rejected e, h ++ [⟨op, arg, .reject e⟩])

/-- `throw e`, or an `await` of a rejected promise. -/
def throw (e : Exn) : Eff W α := fun _ h => ok (.rejected e, h)

/-- `try { body } catch (e) { handler }`. A `Result.fail` inside `body` is leaving the model,
not an exception, and stays a failure. -/
def tryCatch (body : Eff W α) (handler : Exn → Eff W α) : Eff W α := fun o h => do
  let (r, h') ← body o h
  match r with
  | .fulfilled a => ok (.fulfilled a, h')
  | .rejected e => handler e o h'

/-- `try { body } finally { cleanup }`: the cleanup runs on either outcome, and if it
rejects, that rejection replaces the body's. -/
def tryFinally (body : Eff W α) (cleanup : Eff W Unit) : Eff W α := fun o h => do
  let (r, h') ← body o h
  let (c, h'') ← cleanup o h'
  match c with
  | .rejected e => ok (.rejected e, h'')
  | .fulfilled _ => ok (r, h'')

/-- The loop of `Aeneas.Std.loop`, with the history carried along. -/
def loop {γ δ : Type} (body : γ → Eff W (ControlFlow γ δ)) (x : γ) : Eff W δ := fun o h =>
  Aeneas.Std.loop (fun (st : γ × W.Hist) => do
    let (r, h') ← body st.1 o st.2
    match r with
    | .fulfilled (.cont x') => ok (.cont (x', h'))
    | .fulfilled (.done b) => ok (.done (.fulfilled b, h'))
    | .rejected e => ok (.done (.rejected e, h'))) (x, h)

/-! ### Reading a run -/

/-- `m` fulfils with `a` on this oracle and history, and leaves history `h'`. -/
def Fulfils (m : Eff W α) (o : W.Oracle) (h : W.Hist) (a : α) (h' : W.Hist) : Prop :=
  m o h = ok (.fulfilled a, h')

/-- `m` rejects with `e` on this oracle and history, and leaves history `h'`. -/
def Rejects (m : Eff W α) (o : W.Oracle) (h : W.Hist) (e : Exn) (h' : W.Hist) : Prop :=
  m o h = ok (.rejected e, h')

/-- The statement a guarantee about an `async` function is written in: on this oracle and from
this history, every run that completes ends in an outcome and a history satisfying `Q`. Like
`f x ⦃ r => Q r ⦄` for other functions, it says nothing about runs that leave the model, so
"completes" is part of what is proved only when the contract says `= ok ...` instead. -/
def Spec (m : Eff W α) (o : W.Oracle) (h : W.Hist) (Q : Settled α → W.Hist → Prop) : Prop :=
  ∀ r h', m o h = ok (r, h') → Q r h'

@[simp] theorem pure_run (a : α) (o : W.Oracle) (h : W.Hist) :
    (pure a : Eff W α) o h = ok (.fulfilled a, h) := rfl

@[simp] theorem throw_run (e : Exn) (o : W.Oracle) (h : W.Hist) :
    (throw e : Eff W α) o h = ok (.rejected e, h) := rfl

@[simp] theorem lift_run (m : Result α) (o : W.Oracle) (h : W.Hist) :
    (liftM m : Eff W α) o h = (do let a ← m; ok (.fulfilled a, h)) := rfl

theorem bind_run (m : Eff W α) (f : α → Eff W β) (o : W.Oracle) (h : W.Hist) :
    (m >>= f) o h = (do
      let (r, h') ← m o h
      match r with
      | .fulfilled a => f a o h'
      | .rejected e => ok (.rejected e, h')) := rfl

theorem call_run (op : W.Op) (arg : W.Arg op) (o : W.Oracle) (h : W.Hist) :
    (call op arg : Eff W (W.Res op)) o h = match o op arg h with
      | .value v => ok (.fulfilled v, h ++ [⟨op, arg, .value v⟩])
      | .reject e => ok (.rejected e, h ++ [⟨op, arg, .reject e⟩]) := rfl

/-- Code that never waits, bound to what follows: the continuation just runs on its value. -/
@[simp] theorem liftM_ok_bind (a : α) (f : α → Eff W β) :
    ((liftM (ok a : Result α) : Eff W α) >>= f) = f a := by
  apply funext; intro o; apply funext; intro h
  rw [bind_run]; simp

@[simp] theorem pure_bind_eff (a : α) (f : α → Eff W β) : ((pure a : Eff W α) >>= f) = f a := by
  apply funext; intro o; apply funext; intro h
  rw [bind_run]; simp

@[simp] theorem throw_bind (e : Exn) (f : α → Eff W β) :
    ((throw e : Eff W α) >>= f) = (throw e : Eff W β) := by
  apply funext; intro o; apply funext; intro h
  rw [bind_run]; simp

theorem tryCatch_run (b : Eff W α) (k : Exn → Eff W α) (o : W.Oracle) (h : W.Hist) :
    (tryCatch b k) o h = (do
      let (r, h') ← b o h
      match r with
      | .fulfilled a => ok (.fulfilled a, h')
      | .rejected e => k e o h') := rfl

/-- A call that settles leaves exactly one more event, and leaves its answer there. -/
theorem call_hist {op : W.Op} {arg : W.Arg op} {o : W.Oracle} {h h' : W.Hist} {r : Settled (W.Res op)}
    (e : (call op arg : Eff W (W.Res op)) o h = ok (r, h')) :
    h' = h ++ [⟨op, arg, o op arg h⟩] := by
  rw [call_run] at e
  cases ha : o op arg h <;> simp [ha] at e <;> exact e.2.symm

end Eff

/-- What the differential test (see `typescript/differential.mjs`) asks of a run: the model, with an
oracle that replays the answers Node's stand-ins gave, must end as Node did, and its history
must be the calls Node's stand-ins saw. `expected` is `none` when Node did something the model
can't express. As for `Js.agree`, the model may always leave the model (`failed`), but when
it completes, it must agree. -/
def agreeAsync {W : World} {α : Type} [DecidableEq α] (label : String) (r : Result (Settled α × W.Hist))
    (expected : Option (Settled α)) (trace : W.Hist → Bool) : IO Unit :=
  match r.match with
  | .ok (v, h) =>
    let same : Bool := match v, expected with
      | .fulfilled a, some (.fulfilled b) => decide (a = b)
      | .rejected e, some (.rejected e') => decide (e = e')
      | _, _ => false
    IO.println (if same && trace h then s!"PROOFCI_DIFF agree {label}" else s!"PROOFCI_DIFF differ {label}")
  | _ => IO.println s!"PROOFCI_DIFF failed {label}"

end Js
