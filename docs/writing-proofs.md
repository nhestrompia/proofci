# Writing proofs

Practical patterns for proving ProofCI guarantees about Aeneas-translated
Rust. They come from proving properties of real code, including checked
`u128` arithmetic, `?`, closures and library conversions. Give this page to
your coding agent together with the contract and `proofci dev`.

## The shape of the translation

Every function returns `Result T`: `ok v`, or a failure for a panic or an
overflow. `let x ← e` sequences calls. A Rust `Result`/`Option` return value
is an ordinary value inside it, `ok (.Ok v)` or `ok none`. Read the generated
file (`dev` keeps it under the work directory) before writing a statement.

Statements come in two forms:

```lean
-- the call succeeds and the result satisfies P (also: no panic, no overflow)
f x ⦃ r => P r ⦄
-- the call evaluates to exactly this
f x = ok v
```

Prefer `⦃ ⦄`: the `step*` automation works on it.

## The workflow

1. `unfold f` and run `step*`. It steps through calls using `@[step]` lemmas,
   splits `if`/`match`, and discharges arithmetic side conditions with
   `scalar_tac`.
2. Read where it stops in `proofci dev`'s output (errors come first) and add
   what it lacks. Usually that is one of the patterns below.
3. Repeat. Each iteration takes seconds.

## Patterns

**Import the shipped lemmas.** `import ProofciSpecs` gives `step*` lemmas for
integer `From` conversions, `cmp`, `Option::ok_or` and `Result::map_err`.
ProofCI's models of library functions (`abs_diff`, integer `TryFrom`, ...)
come with their own lemmas automatically.

**Give each callee a spec, prove it once, and tag it `@[step]`.** `step*`
then uses it at every call site instead of unfolding:

```lean
@[step] theorem validate_ok (d c : Std.U64) (hd : 0 < d.val) :
    validate d c ⦃ r => r = .Ok () ⦄ := by
  unfold validate; step*
```

**Constants.** `HALF : Result U64 := SCALE / 2` is irreducible. Prove its
value once and use it as a step lemma:

```lean
theorem half_eq : HALF = ok 500000#u64 := by simp only [HALF, SCALE]; rfl
@[step] theorem half_spec : HALF ⦃ h => h.val = 500000 ⦄ := by rw [half_eq]; simp [WP.spec_ok]
```

**Checked arithmetic that cannot overflow.** `checked_mul`/`checked_add`
leave an `Option` whose postcondition is a `match`. Split it; `scalar_tac`
refutes the overflow case from your bounds:

```lean
step*
rcases o with _ | z
· simp only at o_post; scalar_tac      -- overflow is impossible
simp only at o_post                     -- o_post : … ∧ z.val = x.val * y.val ∧ …
step*
```

**Name the steps you refer to.** Plain `step` may reuse or shadow names. Use
`step as ⟨x, x_post⟩` when later lines mention `x` or `x_post`.

**`?` on a known `Ok`.** After `step as ⟨r, r_post⟩` (with `r_post : r = .Ok v`)
and `step as ⟨cf, cf_post⟩` for the `branch`, rewrite and substitute:
`simp only [r_post] at cf_post; subst cf_post`. The `match` then reduces.

**Closures in `Option::map`.** `step*` cannot infer a closure's
postcondition. Case-split on the option, then rewrite with
`core.option.Option.map_some` and the closure's `call_once`.

**Nonlinear arithmetic.** `scalar_tac`/`omega` handle `+`, constants, `/` and
`%` by literals, `min`/`max`. For `x * y / (d * 4)` with variables:

- prove the equation step by step with `rw` (`rw [slope_post, hv, hz]`)
- then `generalize x * y / (d * 4) = S at h ⊢` before `omega`
- for bounds on a division, `Nat.div_le_self`

**Branches by comparison.** `rcases h : compare a.val b.val with _ | _ | _`
gives `.lt`/`.eq`/`.gt` cases. Turn them into facts with
`Nat.compare_eq_lt.mp h` (and `_eq`, `_gt`).

**Big functions.** Prove one exact spec (value per branch) as a lemma, then
derive the contract's statement from it with `WP.spec_mono`:

```lean
apply WP.spec_mono hA
rintro ra ⟨pa, hra, hpa⟩
```

Add `set_option maxHeartbeats 2000000 in` before a large proof if it times out.

**Repeated finishing steps.** A small `macro` with `set_option hygiene false`
can close many similar branches (unfold the helper definition, `rw` the
posts, `split_ifs <;> omega`).

## What the checker rejects

- `sorry`
- extra `axiom`s
- `native_decide`
- proofs of a different statement
- theorems added with kernel checking off
- citing the contract's own `sorry` (importing `Contract`)

Proofs are replayed by the Lean kernel and by nanoda. Helper definitions and
lemmas in `Proofs.lean` or `Proofs/**` are fine.
