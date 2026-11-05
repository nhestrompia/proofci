import F64

/-! # Core: one definition of what the code means (spike)

A small JavaScript semantics: values, a heap of shared objects, exceptions, loops
and calls. Nothing here depends on types or on Aeneas, so unions, `any` and aliasing
need no special treatment. Variables are function-scoped: lowering gives every
declaration its own name.

Spike limits: no closures, classes or async yet. -/

namespace Core

abbrev Loc := Nat

inductive Val where
  | undef | null
  | bool (b : Bool)
  | num (x : F64)
  | big (n : Int)
  | str (s : List Nat)
  | ref (l : Loc)
  | fn (name : String) (env : Val)
  deriving DecidableEq, Repr

inductive Obj where
  | record (fields : List (String × Val))
  | array (items : List Val)
  deriving DecidableEq, Repr

inductive Op where
  | add | sub | mul | lt | le | gt | ge | eq | ne | div | rem
  deriving DecidableEq, Repr

inductive Expr where
  | lit (v : Val)
  | var (x : String)
  | field (e : Expr) (f : String)
  | index (e i : Expr)
  | length (e : Expr)
  | bin (op : Op) (a b : Expr)
  | isNullish (e : Expr)
  | not (e : Expr)
  | neg (e : Expr)
  | math (f : F64 → F64) (e : Expr)
  | or (a b : Expr)
  | and (a b : Expr)
  | cond (c a b : Expr)
  | record (fields : List (String × Expr))
  | array (items : List Expr)
  | call (f : String) (args : List Expr)
  | closure (name : String) (env : Expr)
  | callV (f : Expr) (args : List Expr)
  | callM (o : Expr) (m : String) (args : List Expr)

inductive Stmt where
  | set (x : String) (e : Expr)
  | setField (o : Expr) (f : String) (e : Expr)
  | setIndex (o i e : Expr)
  | expr (e : Expr)
  | push (o e : Expr)
  | ite (c : Expr) (t e : List Stmt)
  | forOf (x : String) (e : Expr) (body : List Stmt)
  | ret (e : Expr)
  | brk
  | throw (e : Expr)

structure Fn where
  params : List String
  body : List Stmt

abbrev Prog := String → Option Fn
abbrev Env := String → Option Val
abbrev Heap := List Obj

def Env.put (env : Env) (x : String) (v : Val) : Env := fun y => if y = x then some v else env y

structure St where
  env : Env
  heap : Heap

/-- How evaluation ended. `stuck` is fuel running out, or a shape the spike doesn't cover. -/
inductive Out (α : Type) where
  | ok (a : α) (s : St)
  | thrown (v : Val) (s : St)
  | stuck

inductive Cmp where
  | normal | brk
  | ret (v : Val)
  deriving DecidableEq, Repr

def typeError : Val := .str [84, 121, 112, 101, 69, 114, 114, 111, 114]

def truthy : Val → Bool
  | .undef | .null => false
  | .bool b => b
  | .num x => match x with
    | .nan | .fin _ 0 => false
    | _ => true
  | .big n => n != 0
  | .str s => !s.isEmpty
  | .ref _ | .fn _ _ => true

def nullish : Val → Bool
  | .undef | .null => true
  | _ => false

def readField (h : Heap) : Val → String → Option Val
  | .ref l, f => match h[l]? with
    | some (.record fs) => some ((fs.lookup f).getD .undef)
    | _ => none
  | _, _ => none

/-- `a < b` on strings: by UTF-16 code unit, a prefix first. -/
def strLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x = y then strLt xs ys else decide (x < y)

def className (s : List Nat) : String := String.ofList (s.map Char.ofNat)

def binary : Op → Val → Val → Option Val
  | .add, .num a, .num b => some (.num (a.add b))
  | .sub, .num a, .num b => some (.num (a.sub b))
  | .mul, .num a, .num b => some (.num (a.mul b))
  | .div, .num a, .num b => some (.num (a.div b))
  | .rem, .num a, .num b => some (.num (a.rem b))
  | .lt, .num a, .num b => some (.bool (a.lt b))
  | .le, .num a, .num b => some (.bool (a.le b))
  | .gt, .num a, .num b => some (.bool (b.lt a))
  | .ge, .num a, .num b => some (.bool (b.le a))
  | .eq, .num a, .num b => some (.bool (a.eq b))
  | .ne, .num a, .num b => some (.bool (!a.eq b))
  | .lt, .str a, .str b => some (.bool (strLt a b))
  | .gt, .str a, .str b => some (.bool (strLt b a))
  | .add, .big a, .big b => some (.big (a + b))
  | .sub, .big a, .big b => some (.big (a - b))
  | .mul, .big a, .big b => some (.big (a * b))
  | .gt, .big a, .big b => some (.bool (decide (a > b)))
  | .lt, .big a, .big b => some (.bool (decide (a < b)))
  | .ge, .big a, .big b => some (.bool (decide (a ≥ b)))
  | .le, .big a, .big b => some (.bool (decide (a ≤ b)))
  | .div, .big a, .big b => if b = 0 then none else some (.big (a.tdiv b))
  | .rem, .big a, .big b => if b = 0 then none else some (.big (a.tmod b))
  | .eq, a, b => some (.bool (decide (a = b)))
  | .ne, a, b => some (.bool (decide (a ≠ b)))
  | _, _, _ => none

mutual

def eval : Nat → Prog → St → Expr → Out Val
  | 0, _, _, _ => .stuck
  | f + 1, p, s, e => match e with
    | .lit v => .ok v s
    | .var x => match s.env x with
      | some v => .ok v s
      | none => .stuck
    | .field o k => match eval f p s o with
      | .ok v s' => match readField s'.heap v k with
        | some r => .ok r s'
        | none => .thrown typeError s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .index o i => match eval f p s o with
      | .ok v s₁ => match eval f p s₁ i with
        | .ok (.num n) s₂ => match v with
          | .ref l => match s₂.heap[l]? with
            | some (.array xs) => .ok ((n.index.bind (xs[·]?)).getD .undef) s₂
            | _ => .thrown typeError s₂
          | _ => .thrown typeError s₂
        | .ok _ s₂ => .thrown typeError s₂
        | .thrown v s₂ => .thrown v s₂
        | .stuck => .stuck
      | .thrown v s₁ => .thrown v s₁
      | .stuck => .stuck
    | .length o => match eval f p s o with
      | .ok (.ref l) s' => match s'.heap[l]? with
        | some (.array xs) => .ok (.num (F64.ofInt xs.length)) s'
        | _ => .thrown typeError s'
      | .ok _ s' => .thrown typeError s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .bin op a b => match eval f p s a with
      | .ok x s₁ => match eval f p s₁ b with
        | .ok y s₂ => match binary op x y with
          | some r => .ok r s₂
          | none => .thrown typeError s₂
        | .thrown v s₂ => .thrown v s₂
        | .stuck => .stuck
      | .thrown v s₁ => .thrown v s₁
      | .stuck => .stuck
    | .isNullish a => match eval f p s a with
      | .ok v s' => .ok (.bool (nullish v)) s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .neg a => match eval f p s a with
      | .ok (.num x) s' => .ok (.num x.neg) s'
      | .ok _ s' => .thrown typeError s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .math g a => match eval f p s a with
      | .ok (.num x) s' => .ok (.num (g x)) s'
      | .ok _ s' => .thrown typeError s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .not a => match eval f p s a with
      | .ok v s' => .ok (.bool (!truthy v)) s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .or a b => match eval f p s a with
      | .ok v s' => if truthy v then .ok v s' else eval f p s' b
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .and a b => match eval f p s a with
      | .ok v s' => if truthy v then eval f p s' b else .ok v s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .cond c a b => match eval f p s c with
      | .ok v s' => if truthy v then eval f p s' a else eval f p s' b
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .record fs => match evalFields f p s fs with
      | .ok vs s' => .ok (.ref s'.heap.length) { s' with heap := s'.heap ++ [.record vs] }
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .array es => match evalList f p s es with
      | .ok vs s' => .ok (.ref s'.heap.length) { s' with heap := s'.heap ++ [.array vs] }
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .closure g e => match eval f p s e with
      | .ok v s' => .ok (.fn g v) s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .callV c args => match eval f p s c with
      | .ok (.fn g env) s₁ => match evalList f p s₁ args with
        | .ok vs s₂ => match p g with
          | some fn => match run f p fn (env :: vs) s₂.heap with
            | .ok v r => .ok v { s₂ with heap := r.heap }
            | .thrown v r => .thrown v { s₂ with heap := r.heap }
            | .stuck => .stuck
          | none => .stuck
        | .thrown v s₂ => .thrown v s₂
        | .stuck => .stuck
      | .ok _ s₁ => .thrown typeError s₁
      | .thrown v s₁ => .thrown v s₁
      | .stuck => .stuck
    | .callM o m args => match eval f p s o with
      | .ok v s₁ => match evalList f p s₁ args with
        | .ok vs s₂ => match readField s₂.heap v "__class" with
          | some (.str c) => match p (className c ++ "." ++ m) with
            | some fn => match run f p fn (v :: vs) s₂.heap with
              | .ok r t => .ok r { s₂ with heap := t.heap }
              | .thrown r t => .thrown r { s₂ with heap := t.heap }
              | .stuck => .stuck
            | none => .thrown typeError s₂
          | _ => .thrown typeError s₂
        | .thrown v s₂ => .thrown v s₂
        | .stuck => .stuck
      | .thrown v s₁ => .thrown v s₁
      | .stuck => .stuck
    | .call g args => match evalList f p s args with
      | .ok vs s' => match p g with
        | some fn => match run f p fn vs s'.heap with
          | .ok v r => .ok v { s' with heap := r.heap }
          | .thrown v r => .thrown v { s' with heap := r.heap }
          | .stuck => .stuck
        | none => .stuck
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck

def evalList : Nat → Prog → St → List Expr → Out (List Val)
  | 0, _, _, _ => .stuck
  | _ + 1, _, s, [] => .ok [] s
  | f + 1, p, s, e :: es => match eval f p s e with
    | .ok v s₁ => match evalList f p s₁ es with
      | .ok vs s₂ => .ok (v :: vs) s₂
      | .thrown v s₂ => .thrown v s₂
      | .stuck => .stuck
    | .thrown v s₁ => .thrown v s₁
    | .stuck => .stuck

def evalFields : Nat → Prog → St → List (String × Expr) → Out (List (String × Val))
  | 0, _, _, _ => .stuck
  | _ + 1, _, s, [] => .ok [] s
  | f + 1, p, s, (k, e) :: es => match eval f p s e with
    | .ok v s₁ => match evalFields f p s₁ es with
      | .ok vs s₂ => .ok ((k, v) :: vs) s₂
      | .thrown v s₂ => .thrown v s₂
      | .stuck => .stuck
    | .thrown v s₁ => .thrown v s₁
    | .stuck => .stuck

def exec : Nat → Prog → St → Stmt → Out Cmp
  | 0, _, _, _ => .stuck
  | f + 1, p, s, c => match c with
    | .set x e => match eval f p s e with
      | .ok v s' => .ok .normal { s' with env := s'.env.put x v }
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .setField o k e => match eval f p s o with
      | .ok (.ref l) s₁ => match eval f p s₁ e with
        | .ok v s₂ => match s₂.heap[l]? with
          | some (.record fs) =>
            .ok .normal { s₂ with heap := s₂.heap.set l (.record ((k, v) :: fs.filter (·.1 != k))) }
          | _ => .thrown typeError s₂
        | .thrown v s₂ => .thrown v s₂
        | .stuck => .stuck
      | .ok _ s₁ => .thrown typeError s₁
      | .thrown v s₁ => .thrown v s₁
      | .stuck => .stuck
    | .setIndex o i e => match eval f p s o with
      | .ok (.ref l) s₁ => match eval f p s₁ i with
        | .ok (.num n) s₂ => match eval f p s₂ e with
          | .ok v s₃ => match s₃.heap[l]? with
            | some (.array xs) => match n.index with
              | some i =>
                if i < xs.length then
                  .ok .normal { s₃ with heap := s₃.heap.set l (.array (xs.set i v)) }
                else .stuck
              | none => .stuck
            | _ => .thrown typeError s₃
          | .thrown v s₃ => .thrown v s₃
          | .stuck => .stuck
        | .ok _ s₂ => .thrown typeError s₂
        | .thrown v s₂ => .thrown v s₂
        | .stuck => .stuck
      | .ok _ s₁ => .thrown typeError s₁
      | .thrown v s₁ => .thrown v s₁
      | .stuck => .stuck
    | .expr e => match eval f p s e with
      | .ok _ s' => .ok .normal s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .push o e => match eval f p s o with
      | .ok (.ref l) s₁ => match eval f p s₁ e with
        | .ok v s₂ => match s₂.heap[l]? with
          | some (.array xs) => .ok .normal { s₂ with heap := s₂.heap.set l (.array (xs ++ [v])) }
          | _ => .thrown typeError s₂
        | .thrown v s₂ => .thrown v s₂
        | .stuck => .stuck
      | .ok _ s₁ => .thrown typeError s₁
      | .thrown v s₁ => .thrown v s₁
      | .stuck => .stuck
    | .ite c t e => match eval f p s c with
      | .ok v s' => execList f p s' (if truthy v then t else e)
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .forOf x e body => match eval f p s e with
      | .ok v s' => iterate f p x v 0 body s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .ret e => match eval f p s e with
      | .ok v s' => .ok (.ret v) s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .brk => .ok .brk s
    | .throw e => match eval f p s e with
      | .ok v s' => .thrown v s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck

def execList : Nat → Prog → St → List Stmt → Out Cmp
  | 0, _, _, _ => .stuck
  | _ + 1, _, s, [] => .ok .normal s
  | f + 1, p, s, c :: cs => match exec f p s c with
    | .ok .normal s' => execList f p s' cs
    | .ok r s' => .ok r s'
    | .thrown v s' => .thrown v s'
    | .stuck => .stuck

/-- `for (const x of v)`: the array is read again on each turn, as an iterator does. -/
def iterate : Nat → Prog → String → Val → Nat → List Stmt → St → Out Cmp
  | 0, _, _, _, _, _, _ => .stuck
  | f + 1, p, x, v, i, body, s => match v with
    | .ref l => match s.heap[l]? with
      | some (.array xs) => match xs[i]? with
        | none => .ok .normal s
        | some item => match execList f p { s with env := s.env.put x item } body with
          | .ok .normal s' => iterate f p x v (i + 1) body s'
          | .ok .brk s' => .ok .normal s'
          | .ok r s' => .ok r s'
          | .thrown t s' => .thrown t s'
          | .stuck => .stuck
      | _ => .thrown typeError s
    | _ => .thrown typeError s

def run : Nat → Prog → Fn → List Val → Heap → Out Val
  | 0, _, _, _, _ => .stuck
  | f + 1, p, fn, args, h =>
    let env : Env := (fn.params.zip args).foldl (fun e (x, v) => e.put x v) (fun _ => none)
    let env := fn.params.foldl (fun e x => if (e x).isSome then e else e.put x .undef) env
    match execList f p { env, heap := h } fn.body with
    | .ok (.ret v) s => .ok v s
    | .ok _ s => .ok .undef s
    | .thrown v s => .thrown v s
    | .stuck => .stuck

end

/-! `async`: a function split at each `await`. A job runs one piece, then waits its turn. -/

structure Job where
  segs : List (List Stmt)
  env : Env

/-- Runs jobs in microtask order: each `await` of a settled value is one turn of the queue. -/
def drain : Nat → Prog → List Job → Heap → Out Unit
  | 0, _, _, _ => .stuck
  | _ + 1, _, [], h => .ok () ⟨fun _ => none, h⟩
  | f + 1, p, j :: rest, h => match j.segs with
    | [] => drain f p rest h
    | seg :: more => match execList f p ⟨j.env, h⟩ seg with
      | .ok .normal s =>
        if more.isEmpty then drain f p rest s.heap
        else drain f p (rest ++ [⟨more, s.env⟩]) s.heap
      | .ok _ s => drain f p rest s.heap
      | .thrown v s => .thrown v s
      | .stuck => .stuck

/-- `Promise.all` over calls: each runs up to its first `await`, in order, then the queue. -/
def startAll (calls : List (List (List Stmt) × List String × List Val)) : List Job :=
  calls.map fun (segs, params, args) =>
    ⟨segs, (params.zip args).foldl (fun e (x, v) => e.put x v) (fun _ => none)⟩

end Core
