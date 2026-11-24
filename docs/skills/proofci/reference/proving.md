# Proof patterns and gotchas (from the pilots)

`docs/proving-typescript.md` + `docs/writing-proofs.md` cover the documented
idioms. This file is what they don't say, verified on real code.

## The reliable opening

- `unfold f; step*` works for toy functions. On real nested `do`-blocks the
  reliable pattern is `simp [WP.spec_ok, f]` (or `simp only [WP.spec_ok]`
  first) plus small equational lemmas rewriting each `Js.*` callee to `ok`:
  `Js.map`→`List.map`, `Js.some_`→`List.any`, `Js.len` (needs a
  `length ≤ 2^53-1` hypothesis — `Js.len` can *fail*).
- Never run full `simp` on `⦃⦄`/spec goals directly: postconditions get
  mangled into degenerate `s ∈ Set.range fun f => ↑f ()` goals. `simp only
  [WP.spec_ok]` first, then equation lemmas.
- `simp only [WP.spec_ok]` fatally errors when nothing is left to rewrite —
  that's progress, not a bug; switch tactics.

## `Bind.bind` vs `Std.bind`

The emitted views use `Bind.bind` (the `>>=` projection) while Aeneas's WP
lemmas (`spec_bind`, `bind_tc_*`) are on `Aeneas.Std.bind` — a different term.
- `open Aeneas.Std Result` makes bare `bind` ambiguous. Qualify.
- `apply WP.spec_bind` won't unify with the real `do`-chain without a bridge;
  write a `Bind.bind`-inversion lemma (`cases x <;> simp_all` on
  `Bind.bind x f = ok r` — ctors are `ret`/`vis`/`div`; `fail` is
  `vis .fail`, not a ctor).
- `cases` on `Result` sees ITree constructors, not `ok`/`fail`.

## Splitting and rewriting

- `split at h` digs under `do`-continuation lambdas where `cases` can't reach;
  order matters: rewrite the scrutinee, unfold, *then* split.
- `cases h : e` substitutes `e` in the goal but NOT in other hypotheses —
  `rw [h] at h1` first.
- `cases h : n.val == 0` fails to match an `if (n.val != 0)` goal; use
  `by_cases hn : n.val = 0` + `simp` (handles `Js.truthyNum`/`if (id)` splits).
- `cases` on a record *projection* (`query.tag`) doesn't reduce `match` —
  `obtain` the structure first.
- `rcases` can't split a `¬P` conjunct — project with `.1`/`.2`.
- `rw` only rewrites the first identical instance; for repeated `ite` with the
  same condition use `simp only [ite_eq_right h]` / `simp only [ite_eq_left h]`
  (the old names `if_neg`/`if_pos`/`dif_pos`/`if_true` are deprecated —
  `ite_eq_right`/`ite_eq_left`/`dite_eq_left`/`ite_true` now).
  `↓reduceIte` handles `true = true` but not `false = true`.
- `obtain` already beta-reduces — no `dsimp` needed.
- `omega` treats `a.val * b.val` as opaque: a hypothesis `rate.val = 0` does not
  simplify `amount.val * rate.val`. `rw [h0] at h` first, then `simp`/`omega`.
- `following` is a Lean keyword — write `«following»` or anonymous `⟨…⟩` ctors.
- `List.all_eq_true` goals yield `decide (c<n) = true` — discharge with
  `decide_eq_true_eq.mpr`.

## `@[step]` lemma coverage (`spike/core/ProofciJs.lean`)

`step*` on emitted code now fires on most `Js.*` primitives. `#[step]` spec
lemmas and their side conditions:

| Primitive | Step lemma | Post | Side conditions |
|---|---|---|---|
| `Js.add`/`sub`/`mul`/`div` | `add_spec`/`sub_spec`/`mul_spec`/`div_spec` | `r.val = x.val ∘ y.val` | operand bounds in range |
| `Js.truncDiv` | `truncDiv_spec` | `r.val = x.val / y.val` | `y.val ≠ 0` |
| `Js.map` | `map_spec` | `ys = xs.map g` | `∀ x ∈ xs, f x = ok (g x)` |
| `Js.filter` | `filter_spec` | `ys = xs.filter p` | `∀ x ∈ xs, f x = ok (p x)` |
| `Js.some_` | `some_spec` | `r = xs.any p` | `∀ x ∈ xs, f x = ok (p x)` |
| `Js.every` | `every_spec` | `r = xs.all p` | `∀ x ∈ xs, f x = ok (p x)` |
| `Js.find` | `find_spec` | `r = xs.find? p` | `∀ x ∈ xs, f x = ok (p x)` |
| `Js.reduce` | `reduce_spec` | `r = xs.foldl g acc` | `∀ a, ∀ x ∈ xs, f a x = ok (g a x)` |
| `Js.indexOf` | `indexOf_val` | `r.val = ↑(idxOf? …).getD 0` | `xs.length ≤ 2^53-1` |
| `Js.len` | `len_spec` | `r.val = ↑xs.length` | `xs.length ≤ 2^53-1` |
| `Js.strIndexOf` | `strIndexOf_spec` | `r.val = match find? …` | `s.length ≤ 2^53-1` |
| `Js.charCodeAt` | `charCodeAt_spec` | `r.val = ↑c` | index hypothesis + `s[i]? = some c` |
| `Js.toLower`/`toUpper` | `toLower_spec`/`toUpper_spec` | ASCII-lower/upper | `s.all (· < 128) = true` |
| `Js.reTest` | `reTest_spec` | `r = m.isSome` | `reOk` witness + `reSearch` outcome |
| `Js.includes` | `includes_eq`/`includes_iff` | `simp` equations | — |
| `Js.startsWith` | `startsWith_eq` (`@[simp]`) | `pre.isPrefixOf s` | — |

For `Js.slice`/`sliceFrom`/`trim`/`split` there are *bounds* lemmas rather
than spec lemmas — `slice_length_le`, `sliceFrom_length_le`, `trim_length_le`
(`(trim s).length ≤ s.length`), `split_length_le` (`(split s sep).length ≤
s.length + 1`), `slice_mem` (elements of a slice are in `xs`), and
`find?_le_length`/`strIndexOf_spec` for `indexOf`. No spec/equational lemmas
yet for `slice`/`trim`/`split`/`endsWith` results themselves.

Still without step lemmas: `Js.recGet`, `Js.setHas`, `Js.strIncludes`,
`Js.endsWith`, `Js.unwrap <nonliteral>`. Workarounds that proved out:

- Inversion lemma + manual `WP.spec_bind` applications, `split` per `if`.
- Big-simp works when every `recGet`/`if` is pinned by a hypothesis:
  `simp [f, hlang, hdef]` closes `f .. ⦃ r => r = d ⦄`.
- `split*` does not exist ("unexpected token '*'"); nested `⦃⦄` doesn't parse;
  `split` can't reach `if`s inside `spec (do let x ← if ...)`.

### Callback premises (`map`/`filter`/`some_`/`every`/`find`/`reduce`)

Each `@[step]` spec takes `∀ x ∈ xs, f x = ok (g x)` — member-bounded on
purpose, since emitted callbacks often only succeed for elements of `xs`
(bounded `Js.add` under the theorem's hypotheses; see the `x + 1` example in
`Spike/PilotGaps.lean`). The `∀ x` versions stay as `*_spec'` corollaries.
Premise goals discharge pointwise — no `funext`:

```lean
  step*
  all_goals first
    | (intro x _hx; rfl)    -- `cb x = ok (p x)` when cb's body IS `p`
    | skip                  -- goals a previous `first` alternative already left
```

For a fold's invariant post, `Js.reduce_spec_inv` is a *named* lemma (not
`@[step]` — its `inv` is a metavariable `step*` can't instantiate); use
`apply Js.reduce_spec_inv` as in `f4` of `PilotGaps.lean`.

### `let x ← if c then a else b` binds

`simp only [Js.bind_tc_ite]` (raw `Bind.bind`, emitted views) or
`simp only [Js.bind_ite]` (hand-written `Std.bind`), then `split <;> step*`.

### Loops: `loop.spec_decr_nat`, positional only

Emitted `for`/`while` loops are `Aeneas.Std.loop`. The invariant lemma takes
its `measure`/`inv`/`post`/`body`/`x`/`hBody`/`hInv` positionally — `refine …
(measure := …)` hits whnf/isDefEq heartbeat timeouts on real bodies; `apply
loop.spec_decr_nat (fun s => s.1) (fun s => …)` does not. Inside `hBody`,
`dsimp only` + `show WP.spec (ok (.done …)) _` / `show WP.spec (Bind.bind …) _`
expose the branch shape; qualify `ControlFlow.done`/`.cont`. `f6` in
`PilotGaps.lean` is the worked example.

### Match atoms, casts and `omega`

`omega` does not split `∧` goals (prove each conjunct), does not reason about
`match`-term atoms in hypotheses (`cases h : scrutinee` first, or rewrite
them away with the step-post `h : x.val = match …`), and cannot see a
match-arm `↑i` cast as non-negative — use `le_trans (by decide)
(Int.natCast_nonneg j)`. After `simp only [hc] at i_post` the post-eq becomes
`i.val = ↑j`/`i.val = -1`; `exact_mod_cast Js.find?_le_length hc` bounds the
`some` case. A `have` written after `step*` lands in the *first* remaining
goal only — put goal-dependent `have`s inside `all_goals first` alternatives
or per-goal `·` bullets. Names bound only in later goals (`l_post`, `r_post`,
`r.val`) can't appear in shared alternatives.

### Literals and `Js.Num` atoms

View numerals are `Js.lit v`, which expands to `Js.Num.mk v (by decide) (by
decide)` — `(Js.lit 5).val = 5` is `decide`/`rfl`-closed (no `_proof_N` terms)
and `simp` reduces `(Js.lit n).val → n` on its own. `Js.lit` needs a literal
`decide` can bound; for a symbolic `v` use `Js.mk`/`Js.mk_ok` or an inline
`if h : -9007199254740991 ≤ v ∧ v ≤ 9007199254740991 then ⟨v, h.1, h.2⟩ else …`.
For `Js.Dbl` literal equality: `simp only [Js.Dbl.lit,
Js.Dbl.mk.injEq]` + `set_option maxHeartbeats` generously.

## `Js.Dbl` (binary64 `number`)

Contracts need `Core.F64` lemmas: `lt_iff`, `le_iff`, `eq_iff`, `isFin`,
`isSafe`, `toRatD`, `*_toRat_nonneg`, `jsround_err_half`. File header:
`set_option exponentiation.threshold 4096` + `maxRecDepth 100000`. Unfold with
`simp [Js.Dbl.add, Js.Dbl.sub, Js.Dbl.mul, Js.Dbl.div, Js.Dbl.math, WP.spec_ok]`
and `Js.Dbl.toRat_eq`. `decide`/`norm_num` fail on `Rat` in `F64` statements —
`rw [*_f, toRat_fin, signed_false]; positivity`.

## Bridge STUCK

"The bridge theorem did not check: STUCK" = the auto-generated faithfulness
proof hit its 120 s cap (or an uncovered form); the function reports
`tested, not proved`. The reason names the construct the proof was working on
(`it was last working on a \`while\` loop (...)`), which points at the statement
to reshape. Fixes that worked:

- `filter().includes().map()` over literal lists → rewrite as `switch` on the
  inductive (proved in ~5 s).
- Splitting a big function into helpers sometimes helps, sometimes doesn't
  (`decidePaginationQuery` stayed stuck) — don't sink time here; the
  differential test still ran and the report is honest.
- Only Node disagreement can produce `failed`; STUCK never means "wrong".

## Iteration speed

Full `dev` runs are slow; copy `proofci/{Contract,Proofs}.lean` into the
`proofci-dev` volume's `lean/` dir and run `lake env lean Proofs.lean` in the
image (~2 s). `dev --json` truncates Lean errors mid-message — use `--show`.

## Translator bugs worth knowing

- `do`-`match` binder scope leak: a `match`-arm pattern variable can shadow a
  parameter in a later branch (a `some value` arm leaked `value` into the
  `none` branch's lambda). Rename the TS parameter if you hit it.

## Honesty

`sorry`, extra `axiom`s, `native_decide`, kernel-check-off theorems, and
importing `Contract` are all rejected. A proof that survives a deliberate
mutation says nothing — try to break the code before finishing.
