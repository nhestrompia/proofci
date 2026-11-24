# Running checks locally and the JSON output

These commands are for coding agents and for anyone who wants the check's result
as data rather than a CI summary. They don't change what the check decides — a
failure is a failure everywhere. To put this in front of a coding agent working
in a repository, paste the block below into that repository's `AGENTS.md`:

```md
## ProofCI

- `proofci scan --repo .` lists which exported functions translate; each refusal
  carries a `hint` — the smallest rewrite the translator accepts.
- `proofci dev --repo . --json` iterates on proofs: Lean errors with file/line.
- `proofci local --repo .` runs the real CI check in the toolchain image before
  you open a pull request; the JSON report goes to stdout.
- Never weaken a contract or edit `proofci.yaml` policy (`targets`, `assumes`,
  `effects`, `require_bridge`, `require_strength`) to make a check pass. Those changes are reported
  to a human approver.
```

## The agent skill

[`skills/proofci/`](skills/proofci/SKILL.md) is an installable agent skill: the
onboarding knowledge from pilot adoptions — the supported TypeScript subset,
every common refusal with the smallest rewrite, the contract-checker's
statement rules, proof patterns that worked, and a `proofci/gaps.jsonl` format
for recording what the skill missed. To install it in a repository a coding
agent works in, copy the directory to `.agents/skills/proofci/` (or your agent's
skills path, e.g. `.devin/skills/proofci/`):

```sh
mkdir -p .agents/skills
cp -r <proofci checkout>/docs/skills/proofci .agents/skills/proofci
```

`constructs.json` in the skill is the machine-readable version of the supported/
refused construct table; `typescript/constructs.test.mjs` keeps it honest
against the translator.

## Commands

```sh
proofci scan --repo <dir> [--package <subdir>] [--vendor <dir>] [--work-dir <dir>]
proofci local --repo <dir> [--base <ref>] [--policy base|head] [--image <tag>] [--scan] [--fetch]
proofci dev  --repo <dir> --json
proofci gaps [<gaps.jsonl> ...]
```

`proofci gaps` aggregates the gap logs (`proofci/gaps.jsonl` in each adopting
repository — one JSON object per refusal/workaround/stuck proof, see the skill)
into a table ranked by time lost, so the constructs to design around (or fix
next) are visible across repositories.

## `proofci scan` — the fast pass

Translates every exported function in the package and prints:

```json
{
  "version": 1,
  "module": "TsBank",
  "functions": [
    { "function": "src/ledger.ts::transfer", "translated": true },
    { "function": "src/util.ts::hash", "translated": false,
      "reason": "src/util.ts:3: `any` is not supported yet",
      "hint": "write the real type",
      "code": "type-any" }
  ],
  "summary": { "total": 2, "translated": 1, "refused": 1,
               "by_code": { "type-any": 1 } }
}
```

Every exported function gets an entry: it either translates or is refused.
`reason` is the unsupported construct with its file and line; `hint` is the
"How to fix" line the report shows (from `typescript/hints.mjs`), and is absent
when there is no suggested rewrite. A refusal only blocks the functions that
reach the unsupported construct — an unsupported type or file never hides the
functions that don't use it.

`code` is a stable, machine-readable name for the refusal, defined in
`typescript/hints.mjs` (`type-<name>` for an unsupported built-in or well-known
type, `type-named` for any adopter-named type, `compile-error`,
`outside-package`, `missing-types`, `null-check`, `optional-chain`,
`in-place-mutation`, `mixed-number-modes`, `unassigned-on-path`,
`returns-nothing`, a kebab-case construct name such as `typeof-expression`,
a fixed-string code such as `rest-parameters` or `module-level-mutable`,
or `other`). Codes never name a variable, member or user type, so a rename
can't move a refusal between buckets. Codes are an interface: they are added
but never renamed, so `summary.by_code` can count missing features across
repositories.

## `report.json` additions

`check`/`local` also report `first_adoption`: `true` when the base branch has
no `proofci.yaml` at all — the pull request introduces ProofCI. The candidate's
manifest is used, every guarantee counts as new (the /-- doc-comment rule and
the planted-defect sweep apply to all of them), and the run is a policy change:
it blocks until a maintainer other than the author approves the whole contract.
The new manifest's `policy.approvers` is not trusted yet; it takes effect once
merged.

## `proofci local` — CI on your machine

Runs `check` inside the toolchain image with the same flags as CI
(`--network none`, dropped capabilities, read-only root). The pull-request
scenario is reproduced with `git`: the trusted base defaults to the merge-base
of HEAD with the remote's default branch (the point your pull request's real
base grew from — an agent that committed its own contract edits can't make HEAD
the trusted base), and `--base` names a different ref when you need one. The
commit used is printed to stderr and in the JSON as `base`. Your working tree,
uncommitted changes included, is the head.

`--policy base` is the default and what CI enforces. `--policy head` takes the
manifest, contract and policy from your working tree — useful while iterating,
and the run's stderr says plainly that the result is not what CI decides.
`--fetch` runs the package install first and keeps the network on for that step
only; it needs a `proofci.yaml`. `--scan` runs `scan` inside the image instead,
so a machine without the toolchain can still list functions.

The report goes to stdout, the human-readable summary to stderr. Exit codes:
`0` verified, `1` a guarantee failed, `2` the run errored. An error or a crash
never prints a passing report. `PROOFCI_*` tuning variables the check honours
(`PROOFCI_BRIDGE_TIMEOUT`, `PROOFCI_BRIDGE_BUDGET`, `PROOFCI_MUTATION_FULL`,
`PROOFCI_MUTANTS`, `PROOFCI_MUTATION_BUDGET`, `PROOFCI_PARALLEL_JUDGES`) are
passed through to the container; no other environment is.

## `report.json` (version 1)

The object `check` and `local` print (`base` is added by `local` only):

| Field | Contents |
|---|---|
| `passed` | `true` only when every guarantee verified and every bridge check passed |
| `base` | The commit `local` checked out as the trusted base |
| `language`, `policy_source`, `policy_changes`, `policy_approvers` | As in CI |
| `guarantees[]` | `target`, `guarantee`, `function`, `theorem`, `status` (`VERIFIED`, `UNPROVEN`, `UNSUPPORTED`, `CONTRACT_STALE`, `ERROR`), `reason`, `hint`, `bridge`, `claim`, `previous_claim`, `statement`, `hypotheses`, `warnings`, `errors` (structured Lean errors, see below) |
| `invalid_contract` | `true` when an approved contract is missing a required `/--` doc comment; blocks like a failed guarantee |
| `downgrades[]` | Functions proved on the base branch but not proved now; an entry the policy's `accept_downgrades` didn't accept blocks the run |
| `stale_accepts[]` | `accept_downgrades` entries that name no downgrade here |
| `escapes[]` | Verified guarantees a planted defect still passed; each names `guarantee`, `theorem`, `function`, `accepts` (one plain sentence per mutant: what the guarantee would also accept) |
| `require_strength` | `true` when the active policy blocks on `escapes` |
| `functions[]` | Per translated function: `function`, `status` (`proved`, `tested, not proved`, `failed`), `reason`, `hint` |
| `disagreements[]` | Inputs where Node and the Lean view differ, as `"<function> [<input>, …]"` strings |
| `bridge_summary` | Counts per bridge status |
| `notes`, `timings_seconds` | Report notes and per-phase seconds |

Structured errors (`errors` on guarantees and contract failures):

```json
{ "file": "proofci/Proofs.lean", "line": 12, "column": 5, "message": "unsolved goals" }
```

`dev --json` prints `{"ok": bool, "unsupported": {target: {reason, hint}},
"errors": [...], "guarantees": [{guarantee, function, theorem, verified, reason, claim, hypotheses}]}`.

The schema is covered by `tests/test_agent_interface.py`.

## Contracts on `number` (doubles)

A function the translator moved to IEEE-754 binary64 (`Js.Dbl`) needs its contract
stated on `Js.Dbl` — a stale `Js.Num` contract is `CONTRACT_STALE` with the
construct that flipped the mode in `reason`. Write exact decimals as
`dbl!"12.99"`; write bounds and monotonicity on `x.f.toRatD` (the exact rational
of a finite double) using the lemmas in `spike/core/F64.lean`, and guard on
`x.f.isFin = true` when the contract needs a finite value. Double proof files
start with `set_option exponentiation.threshold 4096` + `maxRecDepth 100000`;
unfold the view with `simp [Js.Dbl.add, Js.Dbl.sub, Js.Dbl.mul, Js.Dbl.div,
Js.Dbl.math, WP.spec_ok]` and rewrite with `Js.Dbl.toRat_eq` to reach `toRatD`.
See `examples/ts-dbl` for a worked contract and proofs.
