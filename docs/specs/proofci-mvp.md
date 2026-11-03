# ProofCI MVP specification

## Problem

Developers and coding agents change code that already has formally
established properties. Without enforcement, a pull request can silently break
a property, or weaken the requirement itself, and still be merged.

## Scope

ProofCI verifies **explicitly declared properties of selected Rust functions**
on every pull request and merge-queue candidate. It is a verification gate,
not an autonomous theorem prover, and it does not claim to prove whole
applications correct.

- One language: safe, self-contained Rust crates, translated to Lean 4 with
  pinned Charon and Aeneas.
- Distribution: an open-source GitHub Action plus a pinned toolchain image.
  It runs on GitHub-hosted runners or anywhere Docker runs. No hosted service.
- No model calls. The author of the change (often a coding agent) supplies the
  proofs; ProofCI only checks them.

## Interface

- `proofci.yaml` names targets (a Rust function path) and their guarantees
  (a Lean theorem name, required or advisory). It contains no formulas.
- `<lean>/Contract.lean` holds the exact statement of every guarantee, about
  the Lean translation of the crate, ending in `sorry`.
- `<lean>/Proofs.lean` (plus optional `<lean>/Proofs/**`) restates and proves
  them.

## Trust and protection

1. The policy (`proofci.yaml` and `Contract.lean`, including `Contract/**`) is
   read from the base commit. Changes in the candidate are reported and block,
   unless a trusted reviewer other than the author approved the exact
   candidate commit. Only then is the candidate's policy used.
2. The Lean model is always regenerated from the candidate's Rust. Committed
   translations are ignored.
3. Crates with dependencies, build scripts, procedural macros, workspaces or
   `unsafe` are `unsupported`.
4. Every tool that reads candidate input runs inside bubblewrap with no network
   and one writable directory, inside an offline container. The verdict comes
   from `lake comparator`, which builds and exports in its own sandbox. It
   checks that each named theorem has exactly the contract's statement,
   including every constant it mentions (such as the extracted functions),
   uses only `propext`, `Quot.sound` and `Classical.choice`, and is accepted by
   Lean's kernel and nanoda.
5. A contract statement must mention its target function, or the guarantee
   is `contract-stale`. A function whose translation depends on axioms (opaque,
   untranslated code) is `unsupported`.
6. Fail closed: missing proofs, build failures, timeouts and infrastructure
   errors never yield `verified`.

Trusted base: the host and Docker, the pinned image, rustc, Charon, Aeneas and
its Lean library, Lean, nanoda and Mathlib.

## Results

Per guarantee: `verified`, `unproven`, `contract-stale` or `unsupported`, with
a reason. The run passes only if every required guarantee is verified and the
policy is unchanged or approved. Exit codes: 0 pass, 1 blocked, 2
configuration or infrastructure error.

## Acceptance

- The example crate verifies end to end on a GitHub-hosted arm64 runner.
- The scenario suite (`tests/test_scenarios.py`) passes against the real
  toolchain. It covers a buggy implementation, a new overflow, `sorry`, a
  weakened statement, a replaced model, a committed fake translation, a
  weakened policy, a signature change, `unsafe` code and a new dependency.
- A demonstration repository shows the required check blocking a real pull
  request and passing a correct one.

## Later

- An x86_64 image; crates with vendored, pinned dependencies.
- Only re-checking guarantees whose dependencies changed.
- A local `proofci dev` command for editing proofs against the generated model.
- Starter examples for parsers and state machines.
- Optional model-assisted proof repair, still judged by the same kernel check.
