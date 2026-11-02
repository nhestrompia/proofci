inductive Phase where
  | idle
  | running (count : Nat)
  deriving Repr

def advance : Phase → Phase
  | .idle => .running 0
  | .running n => .running (n + 1)
