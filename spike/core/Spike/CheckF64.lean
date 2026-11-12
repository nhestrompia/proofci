import F64
open Core

/-- Each line is `op a b expected`, as decimal bit patterns from Node. -/
def main (args : List String) : IO UInt32 := do
  let lines ← IO.FS.lines args[0]!
  let mut bad := 0
  let mut count := 0
  for line in lines do
    match line.splitOn " " with
    | [op, a, b, r] =>
      let x := F64.ofBits a.toNat!
      let y := F64.ofBits b.toNat!
      let want := F64.ofBits r.toNat!
      let got : F64 := match op with
        | "add" => x.add y | "sub" => x.sub y | "mul" => x.mul y | "div" => x.div y | "rem" => x.rem y
        | "floor" => x.floor | "ceil" => x.ceil | "trunc" => x.trunc | "neg" => x.neg
        | "lt" => if x.lt y then F64.ofInt 1 else F64.ofInt 0
        | "le" => if x.le y then F64.ofInt 1 else F64.ofInt 0
        | "eq" => if x.eq y then F64.ofInt 1 else F64.ofInt 0
        | _ => .nan
      count := count + 1
      if got != want || (got.toBits != want.toBits) then
        bad := bad + 1
        if bad ≤ 10 then IO.println s!"BAD {line} got {got.toBits}"
    | _ => pure ()
  IO.println s!"{count} cases, {bad} disagree"
  return (if bad = 0 then 0 else 1)
