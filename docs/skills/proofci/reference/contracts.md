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
- `f x ≠ ok badval` — "never produces this result". **Weak on its own**: an
  always-`fail` implementation satisfies it. Pair it with a guarantee that `f`
  returns `ok` on the valid inputs (see below).
- `¬∃ r, f x = ok r ∧ P r` — "no returning result violates P" (valid limit).
  Same caveat: an always-`fail` implementation satisfies it — pair it.
- `f x = ok x → ∃ y, f y = ok r ∧ R x r` — relational properties need the
  second call inside the conclusion (∃-witness). Accepted, but the checker
  warns the hypothesis mentions `f` — that warning is what a human reviews.
- `f x ⦃ _ => True ⦄` — "always returns ok". Use it as the pairing partner of
  every `≠`/`¬∃` guarantee: under the same hypotheses, assert the function
  succeeds at all.

## Rejected

- `∀ r, f x = ok r → P r` — `contract-stale`: "the conclusion does not mention
  `f`, so it would not constrain the implementation", plus a warning that a
  hypothesis "may assume what it should prove". The `∀` and the `→` telescope
  into binders, so the checker's conclusion is just `P r` — `f` is gone. This
  holds for *any* `→` after the `∀`: `∀ r, f x = ok r → (r = true ↔ …)` is
  rejected the same way. Restate as `≠`/`¬∃`/equation, or put `↔` inside a
  `⦃⦄` postcondition.
- `f x = ok true → P` — same: `f` appears only in the hypothesis.

## `⦃⦄` is total correctness — the silent trap

`WP.spec (fail e) p ↔ False`, so `f ⦃P⦄` asserts `f` *always returns ok*. For
functions built on `Js.sub` (fails on overflow), `Js.reTest`/`Js.recGet` (can
`fail`/`div`), a guaranteed-ok statement is simply false. "When it returns ok,
P" cannot be stated as `f x = ok r → P` (rejected, above) — use `≠`/`¬∃`, and
remember those hold for an always-fail implementation too: pair each with a
second guarantee that `f` returns `ok` on the inputs it should handle.

## Literals in statements

`Js.Num` is a structure with proof fields, so `f x 0` does not elaborate — write
`f x (Js.Num.mk 0 (of_decide_eq_true rfl) (of_decide_eq_true rfl))` (see
`examples/ts-dates`), or take the value as a hypothesis (`h : rate.val = 0`),
which is usually clearer anyway. Strings are `js!"text"`, doubles `dbl!"12.99"`.

## Paired guarantees and the trivial-implementation check

Guarantees come in pairs, one direction per side of the spec — all in accepted
shapes (checked against the contract checker):

- Boolean decisions: `… ⦃ r => r = true ⦄` under the accept hypotheses **and**
  `… ⦃ r => r = false ⦄` under the reject ones (or the spec equations
  `f x = ok true` / `f x = ok false`).
- Filters/lookups: "kept/found exactly when" — one `⦃⦄` with `↔` inside the
  postcondition: `f xs ⦃ r => ∀ x, x ∈ r ↔ P x ⦄`.
- Parsers/decoders: `f s ⦃ _ => True ⦄` (or a `⦃⦄` result shape) under the
  valid-input hypotheses for "accepts", and `¬∃ r, f s = ok r` under the
  invalid-input hypotheses for "rejects" — the second alone is satisfied by a
  parser that rejects everything.

Then ask: does this also pass for a trivial implementation — `f x = x`, a
constant, always `err`? The `≠`/`¬∃` shapes always pass for `err`; the
ok-guarantee pairing is what rules that out. If the answer is still yes, the
guarantee pins down nothing — add the missing direction or a bound before
writing code.

## Hygiene

- Write **general, quantified guarantees**: the statement must apply the target
  to universally bound variables (`(x : Js.Num)`, `f x ⦃ … ⦄`), not only to
  literals. A guarantee whose every application of the target takes literal
  arguments — `theorem t : f (js!"a.ts") ⦃ r => r = false ⦄` — is labelled
  `scope: example` in the report ("checks one fixed input only") and blocks
  when the policy sets `require_general: true`. A fixed-input case is fine as a
  *supplement* to a quantified guarantee, never as the only statement of a
  behaviour.
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
- When you extract a pure core to satisfy the subset, the original code must
  **call** the extracted function — refactor by delegation, never a parallel
  copy. A copy nothing imports is dead code: ProofCI warns `nothing in the
  repository calls …` next to the target, and the guarantees cover nothing the
  repository ships.
- Never weaken a contract or the policy (`proofci.yaml`) to pass a check.
