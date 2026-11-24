# Guarantee statement shapes (contract checker rules)

The checker only surfaced these at `local` time in the pilots — `dev` reports
"proofs build" for a contract `local` rejects as `contract-stale`. Learn them
here instead of burning a 2.5-minute `local` run.

## The one rule that bites

**The conclusion of every guarantee must mention the target function.**

- `f x ⦃ r => P r ⦄` — **prefer this.** Asserts the call always returns `ok`
  with `r` satisfying `P` (also rules out panic/leaving the model). Strongest.
- `f x = ok <expr>` — a spec equation; good for exact outputs
  (`f x = ok (if ... then decide P else ...)`).
- `f x ≠ ok badval` — "never produces this result".
- `¬∃ r, f x = ok r ∧ P r` — "no returning result violates P" (valid limit).
- `f x = ok x → ∃ y, f y = ok r ∧ R x r` — relational properties need the
  second call inside the conclusion (∃-witness).

## Rejected

- `∀ r, f x = ok r → P r` — `contract-stale`: "the conclusion does not mention
  `f`, so it would not constrain the implementation", plus a warning that a
  hypothesis "may assume what it should prove". This is the only honest shape
  for fallible callees, and it is rejected — restate as `≠`/`¬∃`/equation.
- `f x = ok true → P` — same: `f` appears only in the hypothesis.

## `⦃⦄` is total correctness — the silent trap

`WP.spec (fail e) p ↔ False`, so `f ⦃P⦄` asserts `f` *always returns ok*. For
functions built on `Js.sub` (fails on overflow), `Js.reTest`/`Js.recGet` (can
`fail`/`div`), a guaranteed-ok statement is simply false. "When it returns ok,
P" cannot be stated as `f x = ok r → P` (rejected, above) — use `≠`/`¬∃`.

## Literals in statements

`Js.Num` is a structure with proof fields, so `f x 0` does not elaborate — write
`f x (Js.Num.mk 0 (of_decide_eq_true rfl) (of_decide_eq_true rfl))` (see
`examples/ts-dates`), or take the value as a hypothesis (`h : rate.val = 0`),
which is usually clearer anyway. Strings are `js!"text"`, doubles `dbl!"12.99"`.

## Paired guarantees and the trivial-implementation check

Guarantees come in pairs, one direction per side of the spec:

- Boolean decisions: `… ⦃ r => r = true ⦄` under the accept hypotheses **and**
  `… ⦃ r => r = false ⦄` under the reject ones (or `∀ r, f x = ok r → (r = true ↔ …)`).
- Filters/lookups: "kept/found exactly when" — both `P x → x ∈ result` and
  `x ∈ result → P x`.
- Parsers/decoders: "accepts every valid input" and "rejects every invalid
  input" — a parser that rejects everything satisfies the first alone.

Then ask: does this also pass for a trivial implementation — `f x = x`, a
constant, always `err`? If it does, the guarantee pins down nothing; add the
missing direction or a bound before writing code.

## Hygiene

- A `/-- ... -/` doc comment on every contract theorem is **required** — it is
  the claim the report shows a human. Missing/dropped comments are
  `contract-stale` and block like a failed guarantee.
- `Proofs.lean` cannot import `Contract` — restate hypotheses inline.
- Hypotheses are assumptions about callers; keep them few, checkable, and
  honest in the doc comment. The checker warns when a hypothesis mentions the
  function (it "may assume what it should prove") — that warning fires even on
  the `∃`-restatement shape the checker itself forces; it is a warning, not a
  failure, and it is what a human reviews.
- Safe-integer bounds: `Js.len`-using functions need `xs.length ≤ 2^53-1` (=
  `9007199254740991`) hypotheses. `Js.Dbl` contracts need `x.f.isFin = true`
  guards and `toRatD` reasoning — see proving.md.
- Never weaken a contract or the policy (`proofci.yaml`) to pass a check.
