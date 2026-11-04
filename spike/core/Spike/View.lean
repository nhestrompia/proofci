import Aeneas
import ProofciJs

open Aeneas Aeneas.Std Result

def src.heldout.rangePosition (cell : Js.Str) (start : Js.Str) («end» : Js.Str) : Result (Option Js.Str) := do
  if (Js.strLt cell start = true) ∨ (Js.strLt «end» cell = true) then
    Result.ok none
  else
    if cell = start then
      Result.ok (some (js!"start"))
    else
      if cell = «end» then
        Result.ok (some (js!"end"))
      else
        Result.ok (some (js!"middle"))

