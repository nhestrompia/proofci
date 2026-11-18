import Dyn

namespace Closure
open Core Dyn

set_option maxRecDepth 4096

abbrev renderContextItemsWithStatus.pre (contextItems' : Val) (h : Heap) : Prop :=
  Is h (.arr .any) contextItems'
def renderContextItemsWithStatus (contextItems' : Val) : M Val := do
  return (← (do let r2 := (← (do let r1 := contextItems'; jsMap r1 (fun item' _ => do
      let mut result' ← (do (fun o => field o "content") item')
      if truthy (← (do (fun o => field o "status") item')) then
        result' ← (bin .add result' (← (do pure (← bin .add (← bin .add (str "\n[Status: ") (← toStr (← (do (fun o => field o "status") item')))) (str "]")))))
      return result'))); method .join r2 [(str "\n\n")]))
end Closure
