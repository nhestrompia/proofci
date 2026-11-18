import Dyn

namespace Union
open Core Dyn

set_option maxRecDepth 4096

abbrev isDashboardPrivateKeyOfUser.pre (key' : Val) (userId' : Val) (h : Heap) : Prop :=
  Is h .str key' ∧
  Is h (.union [.str, .num]) userId'
def isDashboardPrivateKeyOfUser (key' : Val) (userId' : Val) : M Val := do
  let parts' ← (do let r1 := key'; method .split r1 [(str ":")])
  return (← (do let a3 := (← (do let a2 := (← (do bin .eq (← (do length parts')) (num 4))); if truthy a2 then (do bin .eq (← (do index parts' (num 0))) (str "af.dashboard.private.v1")) else pure a2)); if truthy a3 then (do bin .eq (← (do index parts' (num 2))) (← (do toStr userId'))) else pure a3))
abbrev idPart.pre (value' : Val) (h : Heap) : Prop :=
  Is h (.union [.undef, .null, .str, .num]) value'
def idPart (value' : Val) : M Val := do
  if truthy (← (do let a1 := (← (do bin .eq value' .null)); if truthy a1 then pure a1 else (do bin .eq value' .undef))) then
    return .null
  let text' ← (do toStr value')
  return (← (do if truthy (← (do bin .eq text' (str ""))) then (pure .null) else (pure text')))
abbrev dashboardPrivateStorageKey.pre (workspaceId' : Val) (userId' : Val) (dashboardViewId' : Val) (h : Heap) : Prop :=
  Is h (.union [.undef, .null, .str]) workspaceId' ∧
  Is h (.union [.undef, .null, .str, .num]) userId' ∧
  Is h (.union [.undef, .null, .str]) dashboardViewId'
def dashboardPrivateStorageKey (workspaceId' : Val) (userId' : Val) (dashboardViewId' : Val) : M Val := do
  let parts' ← (do let x1 := (← (do idPart workspaceId')); let x2 := (← (do idPart userId')); let x3 := (← (do idPart dashboardViewId')); arr ([] ++ [x1] ++ [x2] ++ [x3]))
  if truthy (← (do let r4 := parts'; jsSome r4 (fun part' _ => do
      return (← (do bin .eq part' .null))))) then
    return .null
  return (← (do let r7 := (← (do let x5 := (str "af.dashboard.private.v1"); let x6 ← items parts'; arr ([] ++ [x5] ++ x6))); method .join r7 [(str ":")]))
end Union
