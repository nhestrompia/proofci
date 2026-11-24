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
  same condition use `simp only [if_neg h]` / `simp only [if_pos h]`.
  `↓reduceIte` handles `true = true` but not `false = true`.
- `obtain` already beta-reduces — no `dsimp` needed.
- `omega` treats `a.val * b.val` as opaque: a hypothesis `rate.val = 0` does not
  simplify `amount.val * rate.val`. `rw [h0] at h` first, then `simp`/`omega`.
- `following` is a Lean keyword — write `«following»` or anonymous `⟨…⟩` ctors.
- `List.all_eq_true` goals yield `decide (c<n) = true` — discharge with
  `decide_eq_true_eq.mpr`.

## Missing `@[step]` lemmas — the biggest cost driver

`Js.reTest`, `Js.recGet`, `Js.setHas`, `Js.find`, `Js.strIncludes`,
`Js.startsWith`, `Js.endsWith`, `Js.trim`, `Js.filter`, `Js.split`, `Js.map`,
`Js.some_`, `Js.toUpper`, `Js.unwrap <nonliteral>` have none; `step*` stalls
silently there (also at `let x ← if ...` binds). Workarounds that proved out:

- Inversion lemma + manual `WP.spec_bind` applications, `split` per `if`.
- Reusable lemmas to write once in `Proofs.lean`: `splitGo` result `≤ fuel+1`
  (induction on fuel); `Js.split s sep` parts `≤ s.length+1`;
  `Js.filter f xs` post `ys.length ≤ xs.length` via `WP.spec_bind` induction;
  `Js.sliceFrom` bound via `rw [Js.sliceFrom, Js.bound]; simp [List.length_drop]`.
- Big-simp works when every `recGet`/`if` is pinned by a hypothesis:
  `simp [f, hlang, hdef]` closes `f .. ⦃ r => r = d ⦄`.
- `split*` does not exist ("unexpected token '*'"); nested `⦃⦄` doesn't parse;
  `split` can't reach `if`s inside `spec (do let x ← if ...)`.

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
