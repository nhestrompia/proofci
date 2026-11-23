import Dyn

namespace Fixtures
open Core Dyn

set_option maxRecDepth 4096

abbrev colorIndexes.pre (items' : Val) (h : Heap) : Prop :=
  Is h (.arr (.obj [("empty", (.union [(.lit (.bool false)), (.lit (.bool true))])), ("color", .str)])) items'
def colorIndexes (items' : Val) : M Val := do
  let index' ← cell (num 0)
  let changed' ← cell (.bool false)
  let out' ← (do let r1 := items'; jsMap r1 (fun item' _ => do
      let color' ← (do if truthy (← (do (fun o => field o "empty") item')) then (pure (str "none")) else (do pure (← bin .add (← bin .add (str "c") (← toStr (← (get index')))) (str ""))))
      if truthy (← (do pure (notV (← (do (fun o => field o "empty") item'))))) then
        put index' (← (bin .add (← get index') (num 1)))
      if truthy (← (do bin .eq (← (do (fun o => field o "color") item')) color')) then
        return item'
      put changed' (.bool true)
      return (← (do let s2 ← fieldsOf item'; let f3 := color'; record (mergeFields (mergeFields [] s2) [("color", f3)])))))
  return (← (do if truthy (← (get changed')) then (pure out') else (pure items')))
def Counter.new  : M Val := do
  let this ← record [("__class", (str "Counter"))]
  setField this "n" (num 0)
  return this

def Counter.bump (this : Val) (by' : Val) : M Val := do
  let o1 := this
  setField o1 "n" (← (bin .add (← field o1 "n") by'))
  return (← (do (fun o => field o "n") this))
abbrev bumpBoth.pre (a' : Val) (b' : Val) (h : Heap) : Prop :=
  Is h (.cls "Counter" [("n", .num)]) a' ∧
  Is h (.cls "Counter" [("n", .num)]) b'
def bumpBoth (a' : Val) (b' : Val) : M Val := do
  let _ ← (do let r1 := a'; if (← isMethodOf r1 "Counter" "bump") then Counter.bump r1 (num 1) else (stuck : M Val))
  let _ ← (do let r2 := b'; if (← isMethodOf r2 "Counter" "bump") then Counter.bump r2 (num 1) else (stuck : M Val))
  return (← (do (fun o => field o "n") a'))
abbrev padCode.pre (s' : Val) (h : Heap) : Prop :=
  Is h .str s'
def padCode (s' : Val) : M Val := do
  return (← (do let r1 := s'; method .padStart r1 [(num 4), (str "0")]))
abbrev firstAbove.pre (xs' : Val) (k' : Val) (h : Heap) : Prop :=
  Is h (.arr .num) xs' ∧
  Is h .num k'
def firstAbove (xs' : Val) (k' : Val) : M Val := do
  return (← (do let r1 := xs'; jsFindIndex r1 (fun x' _ => do
      return (← (do bin .gt x' k')))))
abbrev sumIndexed.pre (xs' : Val) (h : Heap) : Prop :=
  Is h (.arr .num) xs'
def sumIndexed (xs' : Val) : M Val := do
  let mut s' := (num 0)
  let mut i' := (num 0)
  for _ in fuel do
    if !(truthy (← (do bin .lt i' (← (do length xs'))))) then break
    s' ← (bin .add s' (← (do index xs' i')))
    i' ← (bin .add i' (num 1))
  return s'
abbrev halvings.pre (n' : Val) (h : Heap) : Prop :=
  Is h .num n'
def halvings (n' : Val) : M Val := do
  let mut k' := (num 0)
  let mut m' := n'
  for _ in fuel do
    if !(truthy (← (do bin .gt m' (num 1)))) then break
    m' ← (do math F64.floor (← (do bin .div m' (num 2))))
    k' ← (bin .add k' (num 1))
  return k'
abbrev lastOf.pre (xs' : Val) (h : Heap) : Prop :=
  Is h (.arr .num) xs'
def lastOf (xs' : Val) : M Val := do
  return (← (do let a2 := (← (do let r1 := xs'; method .«at» r1 [(← (do neg (num 1)))])); if nullish a2 then (pure (num 0)) else pure a2))
abbrev lastCh.pre (s' : Val) (h : Heap) : Prop :=
  Is h .str s'
def lastCh (s' : Val) : M Val := do
  return (← (do let a2 := (← (do let r1 := s'; method .«at» r1 [(← (do neg (num 1)))])); if nullish a2 then (pure (str "")) else pure a2))
abbrev ruler.pre (n' : Val) (h : Heap) : Prop :=
  Is h .num n'
def ruler (n' : Val) : M Val := do
  return (← (do let r1 := (str "-"); method .«repeat» r1 [(← (do bin .rem n' (num 8)))]))
abbrev padRight.pre (s' : Val) (n' : Val) (h : Heap) : Prop :=
  Is h .str s' ∧
  Is h .num n'
def padRight (s' : Val) (n' : Val) : M Val := do
  return (← (do let r1 := s'; method .padEnd r1 [(← (do bin .rem n' (num 12))), (str ".")]))
abbrev flatten.pre (rows' : Val) (h : Heap) : Prop :=
  Is h (.arr (.arr .num)) rows'
def flatten (rows' : Val) : M Val := do
  return (← (do let r1 := rows'; method .flat r1 []))
end Fixtures
