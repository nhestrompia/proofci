import Dyn

namespace Slideshow
open Core Dyn

set_option maxRecDepth 4096

def SlideshowHistory.new (onChange' : Val) : M Val := do
  let this ← record [("__class", (str "SlideshowHistory"))]
  setField this "history" (← (do arr ([])))
  setField this "index" (num 0)
  setField this "onChange" onChange'
  pure ()
  return this

def SlideshowHistory.reset (this : Val) : M Val := do
  let o1 := this
  setField o1 "history" (← (do arr ([])))
  let o2 := this
  setField o2 "index" (num 0)
  return .undef
def SlideshowHistory.queue (this : Val) (asset' : Val) : M Val := do
  let _ ← (do let r1 := (← (do (fun o => field o "history") this)); push r1 asset')
  if truthy (← (do bin .eq (← (do (fun o => field o "index") this)) (← (do bin .sub (← (do length (← (do (fun o => field o "history") this)))) (num 2))))) then
    let o2 := this
    setField o2 "index" (← (bin .add (← field o2 "index") (num 1)))
  return .undef
def SlideshowHistory.next (this : Val) : M Val := do
  if truthy (← (do bin .eq (← (do (fun o => field o "index") this)) (← (do bin .sub (← (do length (← (do (fun o => field o "history") this)))) (num 1))))) then
    return (.bool false)
  let o1 := this
  setField o1 "index" (← (bin .add (← field o1 "index") (num 1)))
  let _ ← (do let r2 := this; (stuck : M Val))
  return (.bool true)
def SlideshowHistory.previous (this : Val) : M Val := do
  if truthy (← (do bin .eq (← (do (fun o => field o "index") this)) (num 0))) then
    return (.bool false)
  let o1 := this
  setField o1 "index" (← (bin .sub (← field o1 "index") (num 1)))
  let _ ← (do let r2 := this; (stuck : M Val))
  return (.bool true)
end Slideshow
