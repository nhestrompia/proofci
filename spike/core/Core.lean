/-! # Core: one definition of what the code means (spike)

A small JavaScript semantics: values, a heap of shared objects, exceptions, loops
and calls. Nothing here depends on types or on Aeneas, so unions, `any` and aliasing
need no special treatment. Variables are function-scoped: lowering gives every
declaration its own name.

Spike limits: numbers are exact integers, not binary64. No closures, classes or async. -/

namespace Core

abbrev Loc := Nat

inductive Val where
  | undef | null
  | bool (b : Bool)
  | num (n : Int)
  | big (n : Int)
  | str (s : List Nat)
  | ref (l : Loc)
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
  | or (a b : Expr)
  | and (a b : Expr)
  | cond (c a b : Expr)
  | record (fields : List (String × Expr))
  | array (items : List Expr)
  | call (f : String) (args : List Expr)
  deriving Repr

inductive Stmt where
  | set (x : String) (e : Expr)
  | setField (o : Expr) (f : String) (e : Expr)
  | setIndex (o i e : Expr)
  | expr (e : Expr)
  | ite (c : Expr) (t e : List Stmt)
  | forOf (x : String) (e : Expr) (body : List Stmt)
  | ret (e : Expr)
  | brk
  | throw (e : Expr)
  deriving Repr

structure Fn where
  params : List String
  body : List Stmt
  deriving Repr

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
  | .num n | .big n => n != 0
  | .str s => !s.isEmpty
  | .ref _ => true

def nullish : Val → Bool
  | .undef | .null => true
  | _ => false

def readField (h : Heap) : Val → String → Option Val
  | .ref l, f => match h[l]? with
    | some (.record fs) => some ((fs.lookup f).getD .undef)
    | _ => none
  | _, _ => none

def binary : Op → Val → Val → Option Val
  | .add, .num a, .num b => some (.num (a + b))
  | .sub, .num a, .num b => some (.num (a - b))
  | .mul, .num a, .num b => some (.num (a * b))
  | .lt, .num a, .num b => some (.bool (decide (a < b)))
  | .le, .num a, .num b => some (.bool (decide (a ≤ b)))
  | .gt, .num a, .num b => some (.bool (decide (a > b)))
  | .ge, .num a, .num b => some (.bool (decide (a ≥ b)))
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
            | some (.array xs) => .ok (if n < 0 then .undef else xs[n.toNat]?.getD .undef) s₂
            | _ => .thrown typeError s₂
          | _ => .thrown typeError s₂
        | .ok _ s₂ => .thrown typeError s₂
        | .thrown v s₂ => .thrown v s₂
        | .stuck => .stuck
      | .thrown v s₁ => .thrown v s₁
      | .stuck => .stuck
    | .length o => match eval f p s o with
      | .ok (.ref l) s' => match s'.heap[l]? with
        | some (.array xs) => .ok (.num xs.length) s'
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
            | some (.array xs) =>
              if 0 ≤ n ∧ n < xs.length then
                .ok .normal { s₃ with heap := s₃.heap.set l (.array (xs.set n.toNat v)) }
              else .stuck
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

end Core
