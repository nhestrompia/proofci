import F64
import ProofciJs

/-! # Core: one definition of what the code means (spike)

A small JavaScript semantics: values, a heap of shared objects, exceptions, loops
and calls. Nothing here depends on types or on Aeneas, so unions, `any` and aliasing
need no special treatment. Variables are function-scoped: lowering gives every
declaration its own name.

Variables are function-scoped: lowering gives every declaration its own name. -/

namespace Core

abbrev Loc := Nat

inductive Val where
  | undef | null
  | bool (b : Bool)
  | num (x : F64)
  | big (n : Int)
  | str (s : List Nat)
  | ref (l : Loc)
  | fn (fname : String) (env : Val)
  deriving DecidableEq, Repr

inductive Obj where
  | record (fields : List (String × Val))
  | array (items : List Val)
  deriving DecidableEq, Repr

inductive Op where
  | add | sub | mul | lt | le | gt | ge | eq | ne | div | rem
  deriving DecidableEq, Repr

/-- Array methods that take a callback. -/
inductive Hof where
  | map | filter | some | every | find
  deriving DecidableEq, Repr

/-- Built-in methods. Each is defined once, on the runtime's own functions, so conformance
to JavaScript is tested against Node rather than proved. -/
inductive Prim where
  | startsWith | endsWith | strIncludes | trim | trimStart | trimEnd
  | toLower | toUpper | slice | sliceFrom | strIndexOf | charAt | numStr
  | min | max | abs | includes | join | split | append
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
  | typeOf (e : Expr)
  | neg (e : Expr)
  | math (f : F64 → F64) (e : Expr)
  | or (a b : Expr)
  | and (a b : Expr)
  | cond (c a b : Expr)
  | record (fields : List (String × Expr))
  | array (items : List Expr)
  | call (f : String) (args : List Expr)
  | closure (fname : String) (env : Expr)
  | callV (f : Expr) (args : List Expr)
  | callM (o : Expr) (m : String) (args : List Expr)
  | prim (op : Prim) (args : List Expr)
  | optField (e : Expr) (f : String)
  | coalesce (a b : Expr)
  /-- `arr.map(x => ...)` with the arrow written in place. `body` names a function table
  entry whose only parameter is `x`, and it runs in the caller's variables. Lowering gives
  every declaration its own name and refuses a callback that assigns outer variables, so this
  is the same as a closure called right here. -/
  | hof (k : Hof) (arr : Expr) (body : String)
  /-- `arr.reduce((acc, x) => ..., init)`, on the same terms. -/
  | reduce (arr init : Expr) (body : String)

inductive Stmt where
  | set (x : String) (e : Expr)
  | setField (o : Expr) (f : String) (e : Expr)
  | setIndex (o i e : Expr)
  | expr (e : Expr)
  | push (o e : Expr)
  | pop (o : Expr)
  | ite (c : Expr) (t e : List Stmt)
  | forOf (x : String) (e : Expr) (body : List Stmt)
  | ret (e : Expr)
  | brk
  | cont
  | whileL (c : Expr) (body step : List Stmt)
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
  | normal | brk | cont
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

/-- `typeof`, as a string of code units. -/
def typeName : Val → List Nat
  | .undef => "undefined".toList.map Char.toNat
  | .null | .ref _ => "object".toList.map Char.toNat
  | .bool _ => "boolean".toList.map Char.toNat
  | .num _ => "number".toList.map Char.toNat
  | .big _ => "bigint".toList.map Char.toNat
  | .str _ => "string".toList.map Char.toNat
  | .fn _ _ => "function".toList.map Char.toNat

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
  | .add, .str a, .str b => some (.str (a ++ b))
  | .le, .str a, .str b => some (.bool (!strLt b a))
  | .ge, .str a, .str b => some (.bool (!strLt a b))
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

/-- A number that is a safe integer, as the runtime's `Num`. -/
def asNum : Val → Option Js.Num
  | .num x => match x with
    | .fin s n =>
      if n % F64.unit = 0 then
        let i := F64.signed s (n / F64.unit)
        if h : -9007199254740991 ≤ i ∧ i ≤ 9007199254740991 then some ⟨i, h.1, h.2⟩ else none
      else none
    | _ => none
  | _ => none

def numVal (a : Js.Num) : Val := .num (F64.ofInt a.val)

def okStr (r : Aeneas.Std.Result (List Nat)) : Option Val :=
  match r.match with
  | .ok r => some (.str r)
  | _ => none

/-- Reads an array of strings. -/
def strsOf : List Val → Option (List (List Nat))
  | [] => some []
  | .str s :: rest => (strsOf rest).map (s :: ·)
  | _ => none

/-- A built-in on values. `none` leaves the model, for example a fractional `slice` bound,
and evaluation stops there, so it can't give a wrong answer. -/
def primV : Prim → Heap → List Val → Option (Val × Heap)
  | .startsWith, h, [.str s, .str t] => some (.bool (Js.startsWith s t), h)
  | .endsWith, h, [.str s, .str t] => some (.bool (Js.endsWith s t), h)
  | .strIncludes, h, [.str s, .str t] => some (.bool (Js.strIncludes s t), h)
  | .trim, h, [.str s] => some (.str (Js.trim s), h)
  | .trimStart, h, [.str s] => some (.str (Js.trimStart s), h)
  | .trimEnd, h, [.str s] => some (.str (Js.trimEnd s), h)
  | .toLower, h, [.str s] => (okStr (Js.toLower s)).map (·, h)
  | .toUpper, h, [.str s] => (okStr (Js.toUpper s)).map (·, h)
  | .slice, h, [.str s, a, b] => match asNum a, asNum b with
    | some a, some b => some (.str (Js.slice s a b), h)
    | _, _ => none
  | .sliceFrom, h, [.str s, a] => (asNum a).map fun a => (.str (Js.sliceFrom s a), h)
  | .slice, h, [.ref l, a, b] => match h[l]?, asNum a, asNum b with
    | some (.array xs), some a, some b => some (.ref h.length, h ++ [.array (Js.slice xs a b)])
    | _, _, _ => none
  | .sliceFrom, h, [.ref l, a] => match h[l]?, asNum a with
    | some (.array xs), some a => some (.ref h.length, h ++ [.array (Js.sliceFrom xs a)])
    | _, _ => none
  | .strIndexOf, h, [.str s, .str t] => match (Js.strIndexOf s t).match with
    | .ok n => some (numVal n, h)
    | _ => none
  | .charAt, h, [.str s, i] => (asNum i).map fun i => (.str (Js.charAt s i), h)
  | .numStr, h, [v] => (asNum v).map fun a => (.str (Js.numStr a), h)
  | .min, h, [a, b] => match asNum a, asNum b with
    | some a, some b => some (numVal (Js.min a b), h)
    | _, _ => none
  | .max, h, [a, b] => match asNum a, asNum b with
    | some a, some b => some (numVal (Js.max a b), h)
    | _, _ => none
  | .abs, h, [a] => (asNum a).map fun a => (numVal (Js.abs a), h)
  | .includes, h, [.str s, .str t] => some (.bool (Js.strIncludes s t), h)
  | .includes, h, [.ref l, .str t] => match h[l]? with
    | some (.array xs) => (strsOf xs).map fun ss => (.bool (Js.includes ss t), h)
    | _ => none
  | .join, h, [.ref l, .str sep] => match h[l]? with
    | some (.array xs) => (strsOf xs).map fun ss => (.str (Js.join ss sep), h)
    | _ => none
  | .append, h, [.ref l, v] => match h[l]? with
    | some (.array xs) => some (.ref h.length, h ++ [.array (xs ++ [v])])
    | _ => none
  | .split, h, [.str s, .str sep] =>
    some (.ref h.length, h ++ [.array ((Js.split s sep).map .str)])
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
      | .ok (.str c) s' => .ok (.num (F64.ofInt c.length)) s'
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
    | .typeOf a => match eval f p s a with
      | .ok v s' => .ok (.str (typeName v)) s'
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
    | .prim op args => match evalList f p s args with
      | .ok vs s' => match primV op s'.heap vs with
        | some (v, h) => .ok v { s' with heap := h }
        | none => .stuck
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .hof k a g => match eval f p s a with
      | .ok (.ref l) s₁ => match p g, s₁.heap[l]? with
        | some fn, some (.array xs) => match fn.params with
          | [x] => match hofRun f p k fn x s₁.env l xs.length 0 [] s₁.heap with
            | .ok v r => .ok v { s₁ with heap := r.heap }
            | .thrown v r => .thrown v { s₁ with heap := r.heap }
            | .stuck => .stuck
          | _ => .stuck
        | _, _ => .stuck
      | .ok _ s₁ => .thrown typeError s₁
      | .thrown v s₁ => .thrown v s₁
      | .stuck => .stuck
    | .reduce a i g => match eval f p s a with
      | .ok (.ref l) s₁ => match eval f p s₁ i with
        | .ok acc s₂ => match p g, s₂.heap[l]? with
          | some fn, some (.array xs) => match fn.params with
            | [y, x] => match reduceRun f p fn y x s₂.env l xs.length 0 acc s₂.heap with
              | .ok v r => .ok v { s₂ with heap := r.heap }
              | .thrown v r => .thrown v { s₂ with heap := r.heap }
              | .stuck => .stuck
            | _ => .stuck
          | _, _ => .stuck
        | .thrown v s₂ => .thrown v s₂
        | .stuck => .stuck
      | .ok _ s₁ => .thrown typeError s₁
      | .thrown v s₁ => .thrown v s₁
      | .stuck => .stuck
    | .optField o k => match eval f p s o with
      | .ok v s' => if nullish v then .ok .undef s' else match readField s'.heap v k with
        | some r => .ok r s'
        | none => .thrown typeError s'
      | .thrown v s' => .thrown v s'
      | .stuck => .stuck
    | .coalesce a b => match eval f p s a with
      | .ok v s' => if nullish v then eval f p s' b else .ok v s'
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
    | .pop o => match eval f p s o with
      | .ok (.ref l) s₁ => match s₁.heap[l]? with
        | some (.array xs) => .ok .normal { s₁ with heap := s₁.heap.set l (.array xs.dropLast) }
        | _ => .thrown typeError s₁
      | .ok _ s₁ => .thrown typeError s₁
      | .thrown v s₁ => .thrown v s₁
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
    | .cont => .ok .cont s
    | .whileL c body step => whileRun f p c body step s
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
          | .ok .cont s' => iterate f p x v (i + 1) body s'
          | .ok .brk s' => .ok .normal s'
          | .ok r s' => .ok r s'
          | .thrown t s' => .thrown t s'
          | .stuck => .stuck
      | _ => .thrown typeError s
    | _ => .thrown typeError s

/-- `while (c) body`, where `step` is what `for` runs after each turn, including after
`continue`. -/
def whileRun : Nat → Prog → Expr → List Stmt → List Stmt → St → Out Cmp
  | 0, _, _, _, _, _ => .stuck
  | f + 1, p, c, body, step, s => match eval f p s c with
    | .ok v s₁ =>
      if truthy v then
        let again := fun s₂ => match execList f p s₂ step with
          | .ok .normal s₃ => whileRun f p c body step s₃
          | .ok r s₃ => .ok r s₃
          | .thrown t s₃ => .thrown t s₃
          | .stuck => .stuck
        match execList f p s₁ body with
        | .ok .normal s₂ => again s₂
        | .ok .cont s₂ => again s₂
        | .ok .brk s₂ => .ok .normal s₂
        | .ok r s₂ => .ok r s₂
        | .thrown t s₂ => .thrown t s₂
        | .stuck => .stuck
      else .ok .normal s₁
    | .thrown t s₁ => .thrown t s₁
    | .stuck => .stuck

/-- One callback turn: reads slot `i` live, as the spec does. A slot that has gone missing
would be a hole, which this model doesn't cover, so it stops. -/
def hofRun : Nat → Prog → Hof → Fn → String → Env → Loc → Nat → Nat → List Val → Heap → Out Val
  | 0, _, _, _, _, _, _, _, _, _, _ => .stuck
  | f + 1, p, k, fn, x, env, l, n, i, out, h =>
    if n ≤ i then
      match k with
      | .map | .filter => .ok (.ref h.length) ⟨env, h ++ [.array out]⟩
      | .some => .ok (.bool false) ⟨env, h⟩
      | .every => .ok (.bool true) ⟨env, h⟩
      | .find => .ok .undef ⟨env, h⟩
    else match h[l]? with
      | some (.array xs) => match xs[i]? with
        | some item => match execList f p ⟨env.put x item, h⟩ fn.body with
          | .ok (.ret v) s => match k with
            | .map => hofRun f p k fn x env l n (i + 1) (out ++ [v]) s.heap
            | .filter => hofRun f p k fn x env l n (i + 1) (if truthy v then out ++ [item] else out) s.heap
            | .some => if truthy v then .ok (.bool true) ⟨env, s.heap⟩ else hofRun f p k fn x env l n (i + 1) out s.heap
            | .every => if truthy v then hofRun f p k fn x env l n (i + 1) out s.heap else .ok (.bool false) ⟨env, s.heap⟩
            | .find => if truthy v then .ok item ⟨env, s.heap⟩ else hofRun f p k fn x env l n (i + 1) out s.heap
          | .ok _ _ => .stuck
          | .thrown v s => .thrown v s
          | .stuck => .stuck
        | none => .stuck
      | _ => .stuck

def reduceRun : Nat → Prog → Fn → String → String → Env → Loc → Nat → Nat → Val → Heap → Out Val
  | 0, _, _, _, _, _, _, _, _, _, _ => .stuck
  | f + 1, p, fn, y, x, env, l, n, i, acc, h =>
    if n ≤ i then .ok acc ⟨env, h⟩
    else match h[l]? with
      | some (.array xs) => match xs[i]? with
        | some item => match execList f p ⟨(env.put y acc).put x item, h⟩ fn.body with
          | .ok (.ret v) s => reduceRun f p fn y x env l n (i + 1) v s.heap
          | .ok _ _ => .stuck
          | .thrown v s => .thrown v s
          | .stuck => .stuck
        | none => .stuck
      | _ => .stuck

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
