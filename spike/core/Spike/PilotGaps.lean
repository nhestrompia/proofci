import ProofciJs
import Spike.Tac

set_option linter.unusedTactic false
open Aeneas Aeneas.Std Result Js

/-! Pilot-shaped end-to-end proofs: one `example` per construct that stalled
`step*` on translated TypeScript in the second pilot. These exercise the
`@[step]` lemmas and the documented workflow on ordinary emitted code, so a
regression in the spec lemmas or the `step*` driver fails the build. -/


-- Pilot-shaped repros for the gap log. Each `example` mirrors one stalled
-- construct; the proof after `:= by` is the now-documented workflow.

-- remeda/changesets/formbricks: emitted `do` blocks elaborate to `Bind.bind`
def f1 (x : Js.Num) : Result Js.Num := do
  let a ← Js.add x (Js.lit 1)
  let b ← Js.mul a (Js.lit 2)
  Js.sub b (Js.lit 3)

example (x : Js.Num) (hx : x.val = 1) : f1 x ⦃ r => r.val = 1 ⦄ := by
  unfold f1
  step*

-- t3code: `let y ← if c then a else b` bind — raw Bind.bind (emitted form)
example (x : Js.Num) (hx : x.val = 3) : WP.spec
    (Bind.bind (if x.val > 0 then Js.add x (Js.lit 1) else Js.sub x (Js.lit 1))
      (fun y => Js.mul y (Js.lit 2)))
    (fun r => r.val = 8) := by
  simp only [Js.bind_tc_ite]
  split <;> step*

-- same inside a hand-written `do` block (Std.bind)
example (x : Js.Num) (hx : x.val = 3) : (do
    let y ← (if x.val > 0 then Js.add x (Js.lit 1) else Js.sub x (Js.lit 1))
    Js.mul y (Js.lit 2)) ⦃ r => r.val = 8 ⦄ := by
  simp only [Js.bind_ite]
  split <;> step*

-- changesets: literals are `Js.lit` — decide/rfl work, no `_proof_N`
example : (Js.lit 5).val = 5 := by decide
example : (Js.lit 5) = ⟨5, by decide, by decide⟩ := rfl

-- formbricks: `Js.Num` projections for omega via `lit_val`
example (x : Js.Num) (h : x.val + (Js.lit 2).val = 7) : x.val = 5 := by
  simp only [Js.lit_val] at h
  omega

-- formbricks: filter + some_ (callback specs; no funext)
def f3 (xs : List Js.Num) : Result Bool := do
  let ys ← Js.filter (fun v => ok (v.val > 0)) xs
  Js.some_ (fun v => ok (v.val > 10)) ys

example (xs : List Js.Num) : f3 xs ⦃ r => r = (xs.filter (fun v => v.val > 0)).any (fun v => v.val > 10) ⦄ := by
  unfold f3
  step*
  all_goals first
    | (intro x; rfl)
    | exact fun v => decide (v.val > 0)
    | skip
  rw [ys_post]
  apply Js.some_spec
  intro x; rfl

-- every + reduce (fold-invariant form `reduce_spec_inv`)
def f4 (xs : List Js.Num) : Result Js.Num := do
  let _ ← Js.every (fun v => ok (v.val ≥ 0)) xs
  Js.reduce (fun a _v => ok a) (Js.lit 0) xs

example (xs : List Js.Num) :
    f4 xs ⦃ r => r.val = 0 ⦄ := by
  unfold f4
  step*
  all_goals first
    | (intro x; rfl)
    | exact fun v => decide (v.val ≥ 0)
    | skip
  apply Js.reduce_spec_inv
  · simp [lit_val]
  · intro a x ha
    simp [WP.spec_ok, ha]

-- indexOf + find + add on Num
def f5 (xs : List Js.Num) : Result Js.Num := do
  let i ← Js.indexOf xs (Js.lit 4)
  let _r ← Js.find (fun v => ok (v.val = 4)) xs
  Js.add i (Js.lit 1)

example (xs : List Js.Num) (hl : xs.length ≤ 9007199254740991) :
    f5 xs ⦃ r => r.val ≥ 0 ⦄ := by
  unfold f5
  step*
  all_goals first
    | (intro x; rfl)
    | exact fun v => decide (v.val = 4)
    | skip
  step*
  all_goals first
    | (rw [i_post]
       cases h : List.idxOf? (Js.lit 4) xs with
       | some j =>
         obtain ⟨hlt, -, -⟩ := List.idxOf?_eq_some_iff.mp h
         simp [lit_val]
         omega
       | none => simp [lit_val])
    | (rw [r_post, i_post]
       cases h : List.idxOf? (Js.lit 4) xs with
       | some j =>
         obtain ⟨hlt, -, -⟩ := List.idxOf?_eq_some_iff.mp h
         simp [lit_val]
         omega
       | none => simp [lit_val])

-- medusa/remeda: emitted for-loop is `Aeneas.Std.loop`; the invariant pattern
-- is `apply loop.spec_decr_nat (measure) (inv)` with positional arguments.
def f6 (n : Nat) : Result Js.Num :=
  Aeneas.Std.loop (fun (state : Nat × Js.Num) =>
    match state with
    | (0, acc) => ok (.done acc)
    | (k + 1, acc) => do
      let next ← Js.add acc (Js.lit 1)
      ok (.cont (k, next)))
    (n, Js.lit 0)

example (n : Nat) (hn : n ≤ 9007199254740991) :
    f6 n ⦃ r => r.val = n ⦄ := by
  unfold f6
  apply loop.spec_decr_nat (fun s => s.1)
    (fun s => s.1 ≤ n ∧ s.2.val = ((n - s.1 : Nat) : Int))
  · rintro ⟨k, acc⟩ ⟨hk, hacc⟩
    match k with
    | 0 =>
      dsimp only
      show WP.spec (ok (ControlFlow.done acc)) _
      simp only [WP.spec_ok]
      omega
    | k + 1 =>
      dsimp only
      show WP.spec (Bind.bind (Js.add acc (Js.lit 1)) (fun next => ok (ControlFlow.cont (k, next)))) _
      simp at hk hacc
      apply spec_bind' (Js.add_spec acc (Js.lit 1) (by simp [lit_val]; omega) (by simp [lit_val]; omega))
      intro next hnext
      simp_all [lit_val]
      omega
  · exact ⟨le_refl n, by simp [lit_val]⟩

-- slice (pure) inside a bound expression + len + add
def f7 (s : Js.Str) : Result Js.Num := do
  let l ← Js.len (Js.slice s (Js.lit 0) (Js.lit 3))
  Js.add l (Js.lit 1)

example (s : Js.Str) (h : s.length ≤ 4503599627370495) :
    f7 s ⦃ r => r.val = ((Js.slice s (Js.lit 0) (Js.lit 3)).length : Int) + 1 ⦄ := by
  unfold f7
  step*
  all_goals first
    | omega
    | simp_all
    | (have hc : (Js.slice s (Js.lit 0) (Js.lit 3)).length ≤ 9007199254740991 :=
         le_trans (Js.slice_length_le s (Js.lit 0) (Js.lit 3)) (le_trans h (by decide))
       omega)
  · have hv : l.val ≤ 9007199254740990 := by
      rw [l_post]
      have hc : (Js.slice s (Js.lit 0) (Js.lit 3)).length ≤ 9007199254740990 :=
        le_trans (Js.slice_length_le s (Js.lit 0) (Js.lit 3)) (le_trans h (by decide))
      exact_mod_cast hc
    rw [← l_post]
    omega

-- strIndexOf_spec's post is `r.val = match find? ...`; deriving bounds uses
-- `find?_le_length` + the cast non-negativity lemmas (the `-1`/`some` cases).
example (s t : Js.Str) (h : s.length ≤ 9007199254740991) :
    Js.strIndexOf s t ⦃ r => -1 ≤ r.val ∧ r.val ≤ (s.length : Int) ⦄ := by
  refine WP.spec_mono (Js.strIndexOf_spec s t h) ?_
  intro r hr
  rw [hr]
  constructor <;> split
  · rename_i x j h_eq
    exact le_trans (by decide) (Int.natCast_nonneg j)
  · omega
  · rename_i x j h_eq
    exact_mod_cast Js.find?_le_length h_eq
  · omega

-- charCodeAt / toLower / startsWith / split / trim / reTest reasoning
example : Js.toLower [65, 66] ⦃ s => s = [97, 98] ⦄ := Js.toLower_spec _ rfl

example (s : Js.Str) : Js.startsWith s [104, 105] = [104, 105].isPrefixOf s := rfl

example (s sep : Js.Str) : (Js.split s sep).length ≤ s.length + 1 := Js.split_length_le s sep

example (s : Js.Str) : (Js.trim s).length ≤ s.length := Js.trim_length_le s

-- reTest: the hypothesis pattern — callers supply an `reOk` witness and the
-- `reSearch` outcome; the spec then reads `m.isSome`.
example (r : Js.Re) (ic : Bool) (s : Js.Str) (m : Option (Nat × Nat))
    (h0 : Js.reOk ic s = true) (hm : Js.reSearch r ic s (s.length + 1) 0 = some m) :
    Js.reTest r ic s ⦃ r' => r' = m.isSome ⦄ := Js.reTest_spec r ic s m h0 hm
