---
name: proofci
description: Adopt ProofCI's formal verification in a TypeScript repository — pick provable functions, satisfy the translator's supported subset, write contract guarantees that pass the checker, prove them in Lean, and read the report. Use when working in a repo that has (or is adding) a proofci.yaml manifest and proofci/*.lean contract files.
---

# ProofCI for coding agents

ProofCI blocks a pull request unless every guarantee in `proofci.yaml` is proved
about a Lean *view* of the code. Agents write the code, the guarantees and the
proofs; a human reads only the final report. Your job: get each guarantee to
`verified` without weakening any contract or policy.

Everything below was verified against the translator. The machine-readable table
of supported and refused constructs is in `constructs.json` next to this file and
is covered by a sync test — trust it over memory.

## Read first

- `reference/commands.md` — the exact commands that work today (no installable
  CLI; `local`/`scan`/`dev` and what a first-adoption run means) and the loop:
  pick → declare → translate → state → prove → check.
- `reference/typescript-subset.md` — what the translator accepts, every common
  refusal, and the smallest rewrite that works.
- `reference/contracts.md` — guarantee statement shapes the contract checker
  accepts and rejects. Read before writing `Contract.lean`.
- `reference/proving.md` — Lean proof patterns and gotchas (`Bind.bind` vs
  `Std.bind`, `simp only [WP.spec_ok]`, missing `Js.*` step lemmas, bridge
  timeouts).
- `reference/report.md` — what `verified`, `tested, not proved` and `blocked`
  mean for the human reading the report.
- `constructs.json` — the tested table: every supported and refused construct
  with a minimal snippet.

## Contract first, then code

Write the guarantees **before** touching the function's code. Preferably hand
it to a separate subagent that sees only the issue/spec and the function's
signature + doc comment — never the implementation — so it cannot write claims
the current code already satisfies instead of claims the spec demands:

1. Guarantee agent: writes the plain-English claims (they become the required
   `/-- ... -/` doc comments) plus the Lean statements, guided by
   `reference/contracts.md`.
2. Code agent: writes/changes the implementation to satisfy them.
3. The code agent **may not weaken** a guarantee afterward; any change to the
   statement goes back through the reviewer.

Write **paired** guarantees — a one-sided claim proves nothing:

- Boolean decisions (permission checks, validators): "returns `true` when …"
  **and** "returns `false` when …".
- Filters/lookups: "kept/found **exactly when** …" (an `∀` both ways).
- Parsers: "accepts every valid input" **and** "rejects every invalid input".

Then the trivial-implementation self-check: *does my guarantee also pass for an
identity function, a constant, or an always-fail?* If yes, it pins down nothing
— strengthen it before writing any code. (CI will run this check too; run it
yourself first.)

## Non-negotiable rules

- Never weaken a contract, edit `proofci.yaml` policy (`targets`, `assumes`,
  `effects`, `require_bridge`, `accept_downgrades`) to make a check pass, or
  remove a `/--` doc comment. Those changes are reported to a human approver.
- Every contract theorem needs a `/-- ... -/` doc comment: the plain-English
  claim a reviewer reads.
- Refactor the *code* to fit the supported subset (extract a pure core), never
  the statement to fit the code.
- If a proof only goes through by making the statement false or vacuous, stop —
  that's a real bug in the code. Report it.

## The gap log — required

Every refusal, workaround, stuck proof or tool failure costs discovery time;
record each so the next adopter starts where you finished. Keep
`proofci/gaps.jsonl` in the adopting repository, one JSON object per line:

```json
{"function": "src/foo.ts::bar", "construct": "typeof guard", "code": "typeof-expression", "refusal": "src/foo.ts:3: `TypeOfExpression` is not supported yet", "workaround": "test for null/undefined instead", "minutes": 8, "resolved": true}
```

Fields: `function` (file::name), `construct` (short name of what blocked you),
`code` (the stable refusal code — copy it verbatim from the `code` field of
the function's `scan --json` entry; `other` when it has none), `refusal` (the message or Lean error), `workaround` (what you did),
`minutes` (time spent, integer), `resolved` (true/false — a stuck bridge or an
unsupported function you abandoned is `false`). Add a line the moment something
blocks or surprises you, not at the end.

`proofci gaps <file> [<file> ...]` aggregates these logs (one argument per repo)
into a table ranked by total minutes lost; `--json` prints the same rows as
JSON for cross-pilot tooling. Rows group by `code` when set, else by normalized
construct text. Run it before choosing targets: constructs ranked high are the
ones to design around first.
