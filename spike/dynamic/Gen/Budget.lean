import Dyn

namespace Budget
open Core Dyn

set_option maxRecDepth 4096

def FormulaEvaluationBudget.new  : M Val := do
  let this ← record [("__class", (str "FormulaEvaluationBudget"))]
  setField this "remaining" (num 100000)
  setField this "remainingRegex" (num 50000000)
  return this

def FormulaEvaluationBudget.consume (this : Val) (amount' : Val) (position' : Val) : M Val := do
  let o1 := this
  setField o1 "remaining" (← (bin .sub (← field o1 "remaining") amount'))
  if truthy (← (do bin .lt (← (do (fun o => field o "remaining") this)) (num 0))) then
    let _ ← (stuck : M Val)
  return .undef
def FormulaEvaluationBudget.consumeRegex (this : Val) (amount' : Val) (position' : Val) : M Val := do
  let o1 := this
  setField o1 "remainingRegex" (← (bin .sub (← field o1 "remainingRegex") amount'))
  if truthy (← (do bin .lt (← (do (fun o => field o "remainingRegex") this)) (num 0))) then
    let _ ← (stuck : M Val)
  return .undef
def FormulaEvaluationBudget.consumeValue (this : Val) (value' : Val) (position' : Val) : M Val := do
  let textLength' ← (do if truthy (← (do bin .eq (← (do (fun o => field o "type") value')) (str "text"))) then (do length (← (do (fun o => field o "value") value'))) else (pure (num 0)))
  let _ ← (do let r1 := this; if (← isMethodOf r1 "FormulaEvaluationBudget" "consume") then FormulaEvaluationBudget.consume r1 (← (do prim .max [(num 1), textLength'])) position' else (stuck : M Val))
  if truthy (← (do let a2 := (← (do bin .eq (← (do (fun o => field o "type") value')) (str "text"))); if truthy a2 then (do (fun o => field o "runs") value') else pure a2)) then
    for run' in (← iter (← (do (fun o => field o "runs") value'))) do
      let _ ← (do let r3 := this; if (← isMethodOf r3 "FormulaEvaluationBudget" "consume") then FormulaEvaluationBudget.consume r3 (← (do bin .add (num 1) (← (do length (← (do (fun o => field o "styles") run')))))) position' else (stuck : M Val))
  if truthy (← (do bin .eq (← (do (fun o => field o "type") value')) (str "list"))) then
    let mut length' ← (do bin .mul (← (do prim .max [(num 0), (← (do bin .sub (← (do length (← (do (fun o => field o "items") value')))) (num 1)))])) (num 2))
    for item' in (← iter (← (do (fun o => field o "items") value'))) do
      length' ← (bin .add length' (← (do let r4 := this; (stuck : M Val))))
    let _ ← (do let r5 := this; if (← isMethodOf r5 "FormulaEvaluationBudget" "consume") then FormulaEvaluationBudget.consume r5 length' position' else (stuck : M Val))
    return length'
  return textLength'
end Budget
