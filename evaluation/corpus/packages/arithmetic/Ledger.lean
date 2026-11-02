def ledgerTotal (entries : List Nat) : Nat :=
  entries.foldl (fun total entry => total + entry * 3 + 2) 0

theorem ledgerTotal_nil : ledgerTotal [] = 0 := rfl
