# ProofCI for coding agents

You write the TypeScript, the guarantees and the proofs; a human reads the CI result
at the end. Everything you need is machine-readable. Read `docs/typescript.md` for the
supported subset and `docs/proving-typescript.md` for writing proofs.

## Commands

All three print JSON on stdout; anything else goes to stderr.

```sh
proofci scan --repo .                    # fast: which exported functions translate, why not
proofci dev --repo . --json              # contract + proof iteration, no CI check
proofci local --repo . --base main       # the exact CI check, in the toolchain image
```

- `scan` lists each exported function with `translated: true|false`. A `false` entry
  carries `reason` (the unsupported construct with its file and line) and `hint` (the
  smallest rewrite the translator accepts, or that there is none yet).
- `dev --json` runs the same contract/proof loop as `proofci dev` but prints
  `{"ok", "unsupported", "errors", "guarantees"}`. Lean errors come with `file`,
  `line`, `column`, `message`.
- `local` runs `check` inside the toolchain image — same sandbox flags, no network —
  and prints `report.json`. The base for policy comes from `git`; everything else is
  your working tree. Add `--fetch` the first time so packages install, then
  `--policy base` is the default (what CI trusts).

Exit codes: `0` every check passed, `1` a check failed, `2` the run itself failed —
a `2` is never a pass.

The JSON schema (version 1) is in `docs/agents.md` and tested in
`tests/test_agent_interface.py`.

## Adding a guarantee to an existing repo

1. `proofci scan --repo <package>` — pick a function that translates, or use the
   hints to decide whether rewriting one is worth it.
2. Add a target to `proofci.yaml` (`language: typescript`, `package`, `lean`, the
   function as `file.ts::name`, each guarantee with an `id` and a `theorem`).
3. Write the theorem in `proofci/Contract.lean` — the Lean name is the file path
   with `.` for `/`, e.g. `src/ledger.ts::transfer` is `src.ledger.transfer` in
   module `import TsBank` (the package name camel-cased). State it about the
   function's *view*: `Js.Num` values, `⦃ r => … ⦄` postconditions.
4. Prove it in `proofci/Proofs.lean`. Iterate with `proofci dev --repo . --json`.
5. `proofci local --repo . --base <branch>` before opening the pull request.

## Rewriting into the supported subset

An `unsupported` entry is not a judgement that the function can't be proved — it
names a construct and the hint names a rewrite. Typical ones: write the real type
instead of `any`, replace a regex with the string operations the subset covers,
split a class method into a module-level function, replace `Date`/`Math.random`
with parameters the caller passes in. Some hints say there is no fix yet; those
functions stay unguarded unless the call is listed under `assumes` or `effects`
in `proofci.yaml`, which is policy — see below.

## Iterating on proofs

`dev --json` reports each guarantee as `verified` true/false with the Lean error
attached (`file`/`line`/`column`/`message`). `sorry` never verifies. The `step*`
tactics described in `docs/proving-typescript.md` do most of the walking; a stuck
proof usually means a hypothesis about safe integers is missing.

## What you must not do

- Don't weaken an existing contract or guarantee to make a proof pass.
- Don't edit policy — `proofci.yaml`'s `assumes`, `effects`, `require_bridge`,
  targets — to unblock yourself. A change to the manifest or contract is a policy
  change the pull request reports, and a human approves it.
- Don't pass a result by any means other than the checks themselves: no editing
  `report.json`, no printing a status by hand, no `--policy head` to approve your
  own changes. A green `local` run means what CI will say on the real base.
