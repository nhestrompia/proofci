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
  `effects`, `require_bridge`) to make a check pass. Those changes are reported
  to a human approver.
```

## Commands

```sh
proofci scan --repo <dir> [--package <subdir>] [--vendor <dir>] [--work-dir <dir>]
proofci local --repo <dir> [--base <ref>] [--policy base|head] [--image <tag>] [--scan] [--fetch]
proofci dev  --repo <dir> --json
```

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
      "hint": "write the real type" }
  ]
}
```

`reason` is the unsupported construct with its file and line; `hint` is the
"How to fix" line the report shows (from `typescript/hints.mjs`), and is absent
when there is no suggested rewrite. A fatal translator failure exits 2.

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
never prints a passing report.

## `report.json` (version 1)

The object `check` and `local` print (`base` is added by `local` only):

| Field | Contents |
|---|---|
| `passed` | `true` only when every guarantee verified and every bridge check passed |
| `base` | The commit `local` checked out as the trusted base |
| `language`, `policy_source`, `policy_changes`, `policy_approvers` | As in CI |
| `guarantees[]` | `target`, `guarantee`, `function`, `theorem`, `status` (`VERIFIED`, `UNPROVEN`, `UNSUPPORTED`, `CONTRACT_STALE`, `ERROR`), `reason`, `hint`, `bridge`, `errors` (structured Lean errors, see below) |
| `functions[]` | Per translated function: `function`, `status` (`proved`, `tested, not proved`, `failed`), `reason`, `hint` |
| `disagreements[]` | Inputs where Node and the Lean view differ, as `"<function> [<input>, …]"` strings |
| `bridge_summary` | Counts per bridge status |
| `notes`, `timings` | Report notes and per-phase seconds |

Structured errors (`errors` on guarantees and contract failures):

```json
{ "file": "proofci/Proofs.lean", "line": 12, "column": 5, "message": "unsolved goals" }
```

`dev --json` prints `{"ok": bool, "unsupported": {target: {reason, hint}},
"errors": [...], "guarantees": [{guarantee, function, theorem, verified, reason}]}`.

The schema is covered by `tests/test_agent_interface.py`.
