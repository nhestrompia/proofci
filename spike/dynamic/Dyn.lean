import Core
import Spike.Safe

/-! # Dyn: JavaScript values and an explicit heap as the Lean view (spike)

Every TypeScript function becomes a Lean function on `Core.Val` in the monad `M`, which
threads the heap and can throw. Types play no part in the meaning; they come back as
preconditions. A step the model doesn't cover is `stuck`, never a guess. -/

namespace Dyn
open Core

inductive R (α : Type) where
  | ok (a : α) (h : Heap)
  | thrown (v : Val) (h : Heap)
  | stuck

def M (α : Type) : Type := Heap → R α

@[inline] def M.pure (a : α) : M α := fun h => .ok a h
@[inline] def M.bind (m : M α) (f : α → M β) : M β := fun h => match m h with
  | .ok a h' => f a h'
  | .thrown v h' => .thrown v h'
  | .stuck => .stuck

instance : Monad M where
  pure := M.pure
  bind := M.bind

def stuck : M α := fun _ => .stuck
def throwV (v : Val) : M α := fun h => .thrown v h
def throwType : M α := throwV typeError
def heap : M Heap := fun h => .ok h h

instance : MonadExceptOf Val M where
  throw := throwV
  tryCatch m k := fun h => match m h with
    | .thrown v h' => k v h'
    | r => r

/-- `m`, started on `h`, returns normally and `P` holds of its result. -/
def Spec (m : M α) (h : Heap) (P : α → Heap → Prop) : Prop :=
  match m h with
  | .ok a h' => P a h'
  | _ => False

@[simp] theorem spec_pure {a : α} {h P} : Spec (pure a : M α) h P ↔ P a h := Iff.rfl
@[simp] theorem spec_bind {m : M α} {f : α → M β} {h P} :
    Spec (m >>= f) h P ↔ Spec m h (fun a h' => Spec (f a) h' P) := by
  show (match M.bind m f h with | .ok a h' => P a h' | _ => False) ↔ _
  unfold Spec M.bind; cases m h <;> simp
@[simp] theorem spec_stuck {h P} : Spec (stuck : M α) h P ↔ False := Iff.rfl
@[simp] theorem spec_throw {v h P} : Spec (throwV v : M α) h P ↔ False := Iff.rfl
@[simp] theorem spec_throwType {h P} : Spec (throwType : M α) h P ↔ False := Iff.rfl
@[simp] theorem spec_heap {h P} : Spec heap h P ↔ P h h := Iff.rfl
@[simp] theorem spec_ite {c : Prop} [Decidable c] {a b : M α} {h P} :
    Spec (if c then a else b) h P ↔ (if c then Spec a h P else Spec b h P) := by split <;> rfl
theorem spec_mono {m : M α} {h P Q} (hm : Spec m h P) (hpq : ∀ a h', P a h' → Q a h') : Spec m h Q := by
  unfold Spec at *; split at hm <;> simp_all

theorem spec_step {m : M α} {f : α → M β} {h a h' P} (e : m h = .ok a h') :
    Spec (m >>= f) h P ↔ Spec (f a) h' P := by
  show (match M.bind m f h with | .ok a h' => P a h' | _ => False) ↔ _
  unfold M.bind; rw [e]; rfl
theorem spec_eq {m : M α} {h a h' P} (e : m h = .ok a h') : Spec m h P ↔ P a h' := by
  unfold Spec; rw [e]

/-! ## Values -/

def num (i : Int) : Val := .num (F64.ofInt i)
/-- A string as JavaScript sees it: UTF-16 code units. -/
def str (s : String) : Val := .str (s.toList.flatMap fun c =>
  if c.toNat < 0x10000 then [c.toNat] else [0xD800 + (c.toNat - 0x10000) / 0x400, 0xDC00 + (c.toNat - 0x10000) % 0x400])

/-- `typeof v`. -/
def typeOf (v : Val) : Val := .str (typeName v)
def bool (v : Val) : Val := .bool (truthy v)
def notV (v : Val) : Val := .bool (!truthy v)

/-- A binary operator. Mixed types would coerce, which the spike doesn't model. -/
def bin (op : Op) (a b : Val) : M Val := match binary op a b with
  | some v => pure v
  | none => stuck

def neg : Val → M Val
  | .num x => pure (.num x.neg)
  | _ => stuck

def math (g : F64 → F64) : Val → M Val
  | .num x => pure (.num (g x))
  | _ => stuck

section
open F64
variable {a b : Int}
private abbrev Safe (x : Int) := -9007199254740991 ≤ x ∧ x ≤ 9007199254740991
@[simp] theorem bin_add_num (h : Safe (a + b)) : bin .add (num a) (num b) = pure (num (a + b)) := by
  simp [bin, binary, num, add_ofInt h.1 h.2]
@[simp] theorem bin_sub_num (h : Safe (a - b)) : bin .sub (num a) (num b) = pure (num (a - b)) := by
  simp [bin, binary, num, sub_ofInt h.1 h.2]
@[simp] theorem bin_lt_num : bin .lt (num a) (num b) = pure (.bool (decide (a < b))) := by simp [bin, binary, num]
@[simp] theorem bin_gt_num : bin .gt (num a) (num b) = pure (.bool (decide (b < a))) := by simp [bin, binary, num]
@[simp] theorem bin_le_num : bin .le (num a) (num b) = pure (.bool (decide (a ≤ b))) := by simp [bin, binary, num]
@[simp] theorem bin_ge_num : bin .ge (num a) (num b) = pure (.bool (decide (b ≤ a))) := by simp [bin, binary, num]
@[simp] theorem bin_eq_num : bin .eq (num a) (num b) = pure (.bool (decide (a = b))) := by simp [bin, binary, num]
@[simp] theorem truthy_bool (x : Bool) : truthy (.bool x) = x := rfl
end

def alloc (o : Obj) : M Val := fun h => .ok (.ref h.length) (h ++ [o])

/-- `o.k`. Fields of primitives and of arrays, other than `length`, aren't modelled. -/
def field (o : Val) (k : String) : M Val := match o with
  | .undef | .null => throwType
  | .ref l => fun h => match h[l]? with
    | some (.record fs) => .ok ((fs.lookup k).getD .undef) h
    | _ => .stuck
  | _ => stuck

theorem field_rec {h : Heap} {l k fs} (hl : h[l]? = some (.record fs)) :
    field (.ref l) k h = .ok ((fs.lookup k).getD .undef) h := by
  show (match h[l]? with | some (.record fs) => _ | _ => _) = _
  rw [hl]

theorem lookup_filter_ne {fs : List (String × Val)} {k k' : String} (hne : k' ≠ k) :
    (fs.filter (fun p => p.1 != k)).lookup k' = fs.lookup k' := by
  induction fs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.filter]
    split <;> simp only [List.lookup] <;> (repeat' split) <;> simp_all

theorem lookup_set_ne {fs : List (String × Val)} {k k' : String} {v : Val} (hne : k' ≠ k) :
    ((k, v) :: fs.filter (fun p => p.1 != k)).lookup k' = fs.lookup k' := by
  have e : (k' == k) = false := by simp [hne]
  simp only [List.lookup, e, lookup_filter_ne hne]

theorem lookup_set_same {fs : List (String × Val)} {k : String} {v : Val} :
    ((k, v) :: fs).lookup k = some v := by simp [List.lookup]

def optField (o : Val) (k : String) : M Val := if nullish o then pure .undef else field o k

def length (o : Val) : M Val := match o with
  | .undef | .null => throwType
  | .str s => pure (num s.length)
  | .ref l => fun h => match h[l]? with
    | some (.array xs) => .ok (num xs.length) h
    | some (.record fs) => .ok ((fs.lookup "length").getD .undef) h
    | none => .stuck
  | _ => stuck

/-- `o[i]`, on arrays and strings by number and on records by string. -/
def index (o i : Val) : M Val := match o, i with
  | .undef, _ | .null, _ => throwType
  | .ref l, .num n => fun h => match h[l]? with
    | some (.array xs) => .ok ((n.index.bind (xs[·]?)).getD .undef) h
    | _ => .stuck
  | .ref l, .str k => fun h => match h[l]? with
    | some (.record fs) => if className k = "__class" then .stuck else .ok ((fs.lookup (className k)).getD .undef) h
    | _ => .stuck
  | .str c, .num n => pure ((n.index.bind (c[·]?)).elim .undef (fun u => .str [u]))
  | _, _ => stuck

def setField (o : Val) (k : String) (v : Val) : M Unit := match o with
  | .undef | .null => throwType
  | .ref l => fun h => match h[l]? with
    | some (.record fs) => .ok () (h.set l (.record ((k, v) :: fs.filter (·.1 != k))))
    | _ => .stuck
  | _ => stuck

theorem setField_rec {h : Heap} {l k v fs} (hl : h[l]? = some (.record fs)) :
    setField (.ref l) k v h = .ok () (h.set l (.record ((k, v) :: fs.filter (·.1 != k)))) := by
  show (match h[l]? with | some (.record fs) => _ | _ => _) = _
  rw [hl]

theorem getElem?_set_ne' {h : Heap} {l m : Loc} {o : Obj} (hne : l ≠ m) : (h.set l o)[m]? = h[m]? :=
  List.getElem?_set_ne hne

def setIndex (o i v : Val) : M Unit := match o, i with
  | .undef, _ | .null, _ => throwType
  | .ref l, .num n => fun h => match h[l]?, n.index with
    | some (.array xs), some j => if j < xs.length then .ok () (h.set l (.array (xs.set j v))) else .stuck
    | _, _ => .stuck
  | _, _ => stuck

/-- The items of an array value. -/
def items (o : Val) : M (List Val) := match o with
  | .undef | .null => throwType
  | .ref l => fun h => match h[l]? with
    | some (.array xs) => .ok xs h
    | _ => .stuck
  | _ => stuck

def arr (xs : List Val) : M Val := alloc (.array xs)
def record (fs : List (String × Val)) : M Val := alloc (.record fs)

/-- `{ ...o, k: v }` style copies: the own fields of a record, in order. -/
def fieldsOf (o : Val) : M (List (String × Val)) := match o with
  | .undef | .null => pure []
  | .ref l => fun h => match h[l]? with
    | some (.record fs) => .ok (fs.filter (·.1 != "__class")) h
    | _ => .stuck
  | _ => stuck

/-- Later keys win, keeping the first position of each key, as object spread does. -/
def mergeFields (a b : List (String × Val)) : List (String × Val) :=
  b.foldl (fun acc (k, v) => if acc.any (·.1 == k) then acc.map (fun p => if p.1 == k then (k, v) else p) else acc ++ [(k, v)]) a

def prim (p : Prim) (args : List Val) : M Val := fun h => match primV p h args with
  | some (v, h') => .ok v h'
  | none => .stuck

def push (o v : Val) : M Val := match o with
  | .undef | .null => throwType
  | .ref l => fun h => match h[l]? with
    | some (.array xs) => .ok (num (xs.length + 1)) (h.set l (.array (xs ++ [v])))
    | _ => .stuck
  | _ => stuck

/-- `Array.isArray`. -/
def isArray (v : Val) : M Val := match v with
  | .ref l => fun h => match h[l]? with
    | some (.array _) => .ok (.bool true) h
    | some (.record _) => .ok (.bool false) h
    | none => .stuck
  | _ => pure (.bool false)

/-- `Number.isInteger`, on any value. -/
def isInteger : Val → Val
  | .num (.fin _ n) => .bool (n % F64.unit = 0)
  | _ => .bool false

/-- `Number.isFinite`, on any value. -/
theorem push_arr {h : Heap} {l xs v} (hl : h[l]? = some (.array xs)) :
    push (.ref l) v h = .ok (num (xs.length + 1)) (h.set l (.array (xs ++ [v]))) := by
  show (match h[l]? with | some (.array xs) => _ | _ => _) = _
  rw [hl]

theorem length_arr {h : Heap} {l xs} (hl : h[l]? = some (.array xs)) :
    length (.ref l) h = .ok (num xs.length) h := by
  show (match h[l]? with | some (.array xs) => _ | some (.record fs) => _ | none => _) = _
  rw [hl]

/-- `Math.min`/`Math.max` on two numbers, keeping `NaN` and the sign of zero. Other
arguments would be coerced, which isn't modelled. -/
def minMax (isMax : Bool) : Val → Val → M Val
  | .num .nan, .num _ | .num _, .num .nan => pure (.num .nan)
  | .num a, .num b => pure (.num (
      if a.lt b then (if isMax then b else a)
      else if b.lt a then (if isMax then a else b)
      else match a with
        | .fin neg 0 => if neg != isMax then a else b
        | _ => a))
  | _, _ => stuck

def abs : Val → M Val
  | .num (.fin _ n) => pure (.num (.fin false n))
  | .num (.inf _) => pure (.num (.inf false))
  | .num .nan => pure (.num .nan)
  | _ => stuck

def isFinite : Val → Val
  | .num (.fin _ _) => .bool true
  | _ => .bool false

/-- `Number(v)` on numbers, and on bigints it holds exactly. -/
def toNum : Val → M Val
  | .num x => pure (.num x)
  | .big n => if n.natAbs ≤ 2 ^ 53 then pure (num n) else stuck
  | _ => stuck

/-- `String(v)`, for the values whose text the model has. -/
def toStr (v : Val) : M Val := prim .toText [v]

/-- The class an object was made by, or nothing. -/
def classOf (o : Val) : M (Option String) := match o with
  | .ref l => fun h => match h[l]? with
    | some (.record fs) => match fs.lookup "__class" with
      | some (.str c) => .ok (some (className c)) h
      | _ => .ok none h
    | _ => .ok none h
  | _ => pure none

/-- `o.m` is the method `m` of class `c`: `o` was made by `c` and has no own field `m`. -/
def isMethodOf (o : Val) (c m : String) : M Bool := match o with
  | .ref l => fun h => match h[l]? with
    | some (.record fs) => .ok (fs.lookup "__class" == some (str c) && (fs.lookup m).isNone) h
    | _ => .ok false h
  | _ => pure false

theorem isMethodOf_rec {h : Heap} {l fs c m} (hl : h[l]? = some (.record fs))
    (hc : fs.lookup "__class" = some (str c)) (hm : fs.lookup m = none) :
    isMethodOf (.ref l) c m h = .ok true h := by
  show (match h[l]? with | some (.record fs) => _ | _ => _) = _
  rw [hl]; simp [hc, hm]

/-! ## Loops and callbacks

The array is read again on each turn, as the iterator and the array methods do. The number
of turns is the starting length; an array that grew past it stops the model. -/

structure Live where
  l : Loc

def iter (o : Val) : M Live := match o with
  | .undef | .null => throwType
  | .ref l => fun h => match h[l]? with
    | some (.array _) => .ok ⟨l⟩ h
    | some (.record _) => .thrown typeError h
    | none => .stuck
  | _ => stuck

def forLoop {β : Type} (l : Loc) (f : Val → β → M (ForInStep β)) : Nat → Nat → β → M β
  | 0, i, b => fun h => match h[l]? with
    | some (.array xs) => if i < xs.length then .stuck else .ok b h
    | _ => .stuck
  | k + 1, i, b => fun h => match h[l]? with
    | some (.array xs) => match xs[i]? with
      | none => .ok b h
      | some x => match f x b h with
        | .ok (.done b') h' => .ok b' h'
        | .ok (.yield b') h' => forLoop l f k (i + 1) b' h'
        | .thrown v h' => .thrown v h'
        | .stuck => .stuck
    | _ => .stuck

instance : ForIn M Live Val where
  forIn x b f := fun h => match h[x.l]? with
    | some (.array xs) => forLoop x.l f xs.length 0 b h
    | _ => .stuck

/-- A callback over an array: `step i item acc` gives the next state or stops. -/
def eachLoop {β : Type} (l : Loc) (step : Nat → Val → β → M (ForInStep β)) : Nat → Nat → β → M β
  | 0, _, b => pure b
  | k + 1, i, b => fun h => match h[l]? with
    | some (.array xs) => match xs[i]? with
      | some x => match step i x b h with
        | .ok (.done b') h' => .ok b' h'
        | .ok (.yield b') h' => eachLoop l step k (i + 1) b' h'
        | .thrown v h' => .thrown v h'
        | .stuck => .stuck
      | none => .stuck
    | _ => .stuck

def each {β : Type} (o : Val) (init : β) (step : Nat → Val → β → M (ForInStep β)) : M β := do
  let xs ← items o
  match o with
  | .ref l => eachLoop l step xs.length 0 init
  | _ => stuck

def jsMap (o : Val) (f : Val → Val → M Val) : M Val := do
  let out ← each o [] fun i x acc => do return .yield (acc ++ [← f x (num i)])
  arr out

def jsFilter (o : Val) (f : Val → Val → M Val) : M Val := do
  let out ← each o [] fun i x acc => do return .yield (if truthy (← f x (num i)) then acc ++ [x] else acc)
  arr out

def jsForEach (o : Val) (f : Val → Val → M Val) : M Val := do
  each o () fun i x _ => do let _ ← f x (num i); return .yield ()
  return .undef

def jsSome (o : Val) (f : Val → Val → M Val) : M Val := do
  let r ← each o false fun i x _ => do return if truthy (← f x (num i)) then .done true else .yield false
  return .bool r

def jsEvery (o : Val) (f : Val → Val → M Val) : M Val := do
  let r ← each o true fun i x _ => do return if truthy (← f x (num i)) then .yield true else .done false
  return .bool r

def jsFind (o : Val) (f : Val → Val → M Val) : M Val :=
  each o .undef fun i x _ => do return if truthy (← f x (num i)) then .done x else .yield .undef

def jsReduce (o : Val) (f : Val → Val → Val → M Val) (init : Val) : M Val :=
  each o init fun i x acc => do return .yield (← f acc x (num i))

/-! ## Methods, chosen by what the receiver is at run time -/

inductive Meth where
  | startsWith | endsWith | includes | trim | toLowerCase | toUpperCase | slice | indexOf
  | lastIndexOf | charAt | charCodeAt | split | join | concat | replaceAll | substring
  deriving DecidableEq, Repr

def method (m : Meth) (o : Val) (args : List Val) : M Val := match o, m, args with
  | .str _, .startsWith, [a] => prim .startsWith [o, a]
  | .str _, .endsWith, [a] => prim .endsWith [o, a]
  | .str _, .includes, [a] => prim .strIncludes [o, a]
  | .str _, .trim, [] => prim .trim [o]
  | .str _, .toLowerCase, [] => prim .toLower [o]
  | .str _, .toUpperCase, [] => prim .toUpper [o]
  | .str _, .slice, [a] => prim .sliceFrom [o, a]
  | .str _, .slice, [a, b] => prim .slice [o, a, b]
  | .str _, .indexOf, [a] => prim .strIndexOf [o, a]
  | .str _, .lastIndexOf, [a] => prim .strLastIndexOf [o, a]
  | .str _, .charAt, [a] => prim .charAt [o, a]
  | .str _, .charCodeAt, [a] => prim .charCodeAt [o, a]
  | .str _, .split, [a] => prim .split [o, a]
  | .str _, .replaceAll, [a, b] => prim .replaceAll [o, a, b]
  | .str _, .substring, [a, b] => prim .substring [o, a, b]
  | .ref _, .includes, [a] => prim .includes [o, a]
  | .ref _, .join, [a] => prim .join [o, a]
  | .ref _, .slice, [a] => prim .sliceFrom [o, a]
  | .ref _, .slice, [a, b] => prim .slice [o, a, b]
  | .ref _, .indexOf, [a] => prim .indexOfStr [o, a]
  | .ref _, .concat, [a] => prim .concat [o, a]
  | .undef, _, _ | .null, _, _ => throwType
  | _, _, _ => stuck

/-! ## Closures that assign the variables they capture

Such a variable lives in a heap cell, so the function and the closure share it. -/

def cell (v : Val) : M Loc := fun h => .ok h.length (h ++ [.array [v]])
def get (c : Loc) : M Val := fun h => match h[c]? with
  | some (.array [v]) => .ok v h
  | _ => .stuck
def put (c : Loc) (v : Val) : M Unit := fun h => match h[c]? with
  | some (.array [_]) => .ok () (h.set c (.array [v]))
  | _ => .stuck

/-! ## TypeScript types, as preconditions -/

inductive Ty where
  | any | undef | null | bool | num | str | big
  | lit (v : Val)
  | arr (t : Ty)
  | obj (fs : List (String × Ty))
  | cls (c : String) (fs : List (String × Ty))
  | union (ts : List Ty)
  deriving Repr

/-- `v` has type `t` in `h`. Records may have more fields than the type lists. -/
def Ty.has (h : Heap) : Nat → Ty → Val → Bool
  | 0, _, _ => false
  | _ + 1, .any, _ => true
  | _ + 1, .undef, v => v == .undef
  | _ + 1, .null, v => v == .null
  | _ + 1, .bool, v => (v matches .bool _)
  | _ + 1, .num, v => (v matches .num _)
  | _ + 1, .str, v => (v matches .str _)
  | _ + 1, .big, v => (v matches .big _)
  | _ + 1, .lit w, v => v == w
  | k + 1, .arr t, .ref l => match h[l]? with
    | some (.array xs) => xs.attach.all fun ⟨x, _⟩ => Ty.has h k t x
    | _ => false
  | k + 1, .obj fs, .ref l => match h[l]? with
    | some (.record gs) => fs.all fun (f, t) => Ty.has h k t ((gs.lookup f).getD .undef)
    | _ => false
  | k + 1, .cls c fs, .ref l => match h[l]? with
    | some (.record gs) => gs.lookup "__class" == some (Dyn.str c) && fs.all fun (f, t) => Ty.has h k t ((gs.lookup f).getD .undef)
    | _ => false
  | k + 1, .union ts, v => ts.any fun t => Ty.has h k t v
  | _ + 1, _, _ => false

abbrev Is (h : Heap) (t : Ty) (v : Val) : Prop := Ty.has h 32 t v = true

/-! ## Reading results, for the comparison with Node -/

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
    | some (.array xs) => "[" ++ ",".intercalate (xs.map fun x => showVal f h x) ++ "]"
    | some (.record fs) =>
      let sorted := ((fs.filter (·.1 != "__class")).toArray.qsort (fun a b => a.1 < b.1)).toList
      "{" ++ ",".intercalate (sorted.map fun (k, v) => k ++ ":" ++ showVal f h v) ++ "}"
    | none => "?"

/-- The result and every argument afterwards, so writes through shared objects are compared too. -/
def report (r : R Val) (args : List Val) : String :=
  let tail (h : Heap) := "|" ++ "|".intercalate (args.map (showVal 50 h))
  match r with
  | .ok v h => showVal 50 h v ++ tail h
  | .thrown _ h => "throw" ++ tail h
  | .stuck => "stuck"

end Dyn
