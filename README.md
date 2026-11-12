<img src="assets/icon.svg" width="64" height="64" alt="">

# ProofCI

> Tests check examples. ProofCI checks that your rules hold for every input, on every pull request.

Write down what your Rust code must always do, prove it in [Lean](https://lean-lang.org),
and make it a required check. Any pull request that breaks a rule is blocked,
whether a person or a coding agent wrote it.

It's a free GitHub Action. There is no service to sign up for and nothing to host.

```
PR #42 · ProofCI

✅ fees/fee-capped            ledger::calculate_fee   verified
✅ fees/zero-amount           ledger::calculate_fee   verified
❌ transfer/conservation      ledger::transfer        unproven
✅ transfer/rejects-overdraft ledger::transfer        verified
```

See it on real pull requests in the [demo repository](https://github.com/nhestrompia/proofci-demo/pulls).

## How it works

Three files sit next to your crate:

```
proofci.yaml             which guarantees are required
proofci/Contract.lean    what they mean (protected: read from the base branch)
proofci/Proofs.lean      why they hold (updated in the PR, for example by your agent)
```

A guarantee is a Lean statement about your Rust function:

```lean
/-- Never panics, and a successful transfer conserves the total balance. -/
theorem transfer_conserves (a : Accounts) (amount : Std.U64) :
    transfer a amount ⦃ r => ∀ b, r = some b → b.from.val + b.to.val = a.from.val + a.to.val ⦄
```

On every pull request, ProofCI:

1. **Translates the PR's Rust into Lean** with [Charon](https://github.com/AeneasVerif/charon)
   and [Aeneas](https://github.com/AeneasVerif/aeneas). Committed translations are ignored.
2. **Takes the rules from the protected base branch,** so a PR can't weaken its own rules.
3. **Checks the proofs** with Lean's kernel and an independent checker (nanoda).
   `sorry`, extra axioms and proofs of a different statement are rejected.

ProofCI doesn't write proofs and doesn't need to trust whoever does. Your coding
agent can write them; they either check or they don't.

## Add it to a repository

Follow [Getting started](docs/getting-started.md). The workflow is short:

```yaml
name: ProofCI
on:
  pull_request_target:          # the workflow and rules come from the base branch
    types: [opened, synchronize, reopened]
  merge_group:
  push:
    branches: [main]
permissions:
  contents: read
  pull-requests: read
jobs:
  proofci:
    runs-on: ubuntu-latest      # any Linux runner, x86_64 or arm64
    timeout-minutes: 30
    steps:
      - uses: nhestrompia/proofci@v0.1.1
```

Then make `ProofCI / proofci` a required status check. A typical check takes about a minute.

## Results

| Status | Meaning |
|---|---|
| `verified` | The kernel accepted a proof of the exact protected statement |
| `unproven` | The proof is missing, uses `sorry`, proves something else, or no longer checks |
| `contract-stale` | The statement no longer fits the code (for example, a changed signature); a maintainer updates it |
| `unsupported` | The code can't be translated; the report shows the source line |

Any of these except `verified` blocks a required guarantee. Removing a guarantee
or editing the contract also blocks, until someone allowed by
`policy.approvers` in `proofci.yaml` approves that exact commit.

## What's supported

- **Crates:** single packages and workspace members, path and crates.io
  dependencies pinned by `Cargo.lock`, build scripts and proc macros.
- **Code in verified functions:** integers up to 128 bits, structs, enums,
  `Option`/`Result`, `?`, closures, loops, `Vec`, borrows. Only what those
  functions reach is translated, so async, I/O or `unsafe` elsewhere in the crate is fine.
- **Guarantees:** anything Lean can state, such as postconditions, invariants, or
  "never panics or overflows".

**Not supported:**

- Other languages. TypeScript is [experimental](docs/typescript.md#status-experimental): it is not in a release and covers a small share of real code. Each function a guarantee names is reported as *proved* (a generated theorem, checked on every run, ties its Lean view to a model of JavaScript), *tested, not proved* (the view is only compared with Node on generated inputs, as for `async` code, which has no bridge yet), or *failed* (Node disagrees). `require_bridge` in `proofci.yaml` makes *tested, not proved* block
- Git dependencies and `[patch]`
- Verified functions that reach raw pointers, threads, I/O or async, or call into
  a dependency's functions

**What "verified" means:** the statement holds for the Rust code as translated
by the pinned toolchain. Charon, Aeneas and rustc are trusted, along with ProofCI's
[models](proofci/models.py) of some standard-library functions, which the report lists.
A guarantee is only as good as its statement, so review contracts like code.

## Docs

- [Getting started](docs/getting-started.md): from an empty repository to a required check
- [Writing proofs](docs/writing-proofs.md): patterns worth giving to your coding agent
- [Security model](SECURITY.md): what it defends against and what it trusts
- [Development](docs/development.md): the toolchain, tests and CI
- Examples: [`examples/bank`](examples/bank), [`examples/ledger`](examples/ledger)

## License

MIT. See [LICENSE](LICENSE).
