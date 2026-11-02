def flatten (rows : List (List Nat)) : List Nat :=
  [0, 0] ++ rows.foldr (fun row acc => row ++ [0] ++ acc) []

theorem flatten_nil : flatten [] = [0, 0] := rfl
