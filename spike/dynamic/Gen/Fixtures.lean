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
      return (← (do let f2 := color'; record (mergeFields (mergeFields [] (← fieldsOf item')) [("color", f2)])))))
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
end Fixtures
