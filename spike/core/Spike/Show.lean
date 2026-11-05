import Core
import Spike.Gen
open Core

namespace Spike

/-- The text form `mk.mjs` gives a JavaScript value. -/
def showVal : Nat → Heap → Val → String
  | 0, _, _ => "?"
  | _ + 1, _, .undef => "undefined"
  | _ + 1, _, .null => "null"
  | _ + 1, _, .bool b => toString b
  | _ + 1, _, .num x => if x == .nan then "NaN" else s!"#{x.toBits}"
  | _ + 1, _, .big n => s!"{n}n"
  | _ + 1, _, .str s => "s[" ++ ",".intercalate (s.map toString) ++ "]"
  | f + 1, h, .ref l => match h[l]? with
    | some (.array xs) => "[" ++ ",".intercalate (xs.attach.map fun x => showVal f h x.1) ++ "]"
    | some (.record fs) =>
      let sorted := (fs.toArray.qsort (fun a b => a.1 < b.1)).toList
      "{" ++ ",".intercalate (sorted.map fun (k, v) => k ++ ":" ++ showVal f h v) ++ "}"
    | none => "?"

def report (fn : Fn) (args : List Val) (heap : Heap) : String :=
  let p := Gen.prog
  let tail (h : Heap) := "|" ++ "|".intercalate (args.map (showVal 50 h))
  match run 2000 p fn args heap with
  | .ok v s => "CORE " ++ showVal 50 s.heap v ++ tail s.heap
  | .thrown _ s => "CORE throw" ++ tail s.heap
  | .stuck => "CORE stuck"

end Spike
