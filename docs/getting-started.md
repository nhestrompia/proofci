# Getting started

This walks through adding ProofCI to a Rust repository, from nothing to a
required check that blocks a pull request breaking a proved guarantee. You
need Docker locally. The example is a crate `bank` with a function
`bank::withdraw`.

## 1. Pick a function and a guarantee

Good first guarantees are about pure logic:

- arithmetic that must not overflow or panic
- a result that stays within bounds
- a state change that conserves a total
- a rejection that must happen

Pick a function whose behaviour you can state precisely in one sentence:

> `withdraw(balance, amount)` never panics, and returns `None` exactly when `amount > balance`.

ProofCI translates only what that function calls. The rest of the crate can
use async, I/O, FFI or `unsafe`. The function itself must stay within what
Aeneas translates: integers, structs, enums, `Option`/`Result`, `?`, loops,
`Vec`, references, closures.

## 2. Declare it in `proofci.yaml`

At the repository root:

```yaml
version: 1
crate: .              # directory of the Cargo package (a workspace member is fine)
lean: proofci         # where Contract.lean and Proofs.lean live

targets:
  - id: withdraw
    function: bank::withdraw          # crate name (with _ for -) :: path
    guarantees:
      - id: rejects-overdraft
        theorem: withdraw_rejects_overdraft
      - id: exact
        theorem: withdraw_exact

# Optional: who may approve a pull request that changes this file or the contract.
policy:
  approvers: [your-github-login]
```

## 3. See the Lean translation

If the crate has crates.io dependencies, download them once (this step needs
network; everything else runs offline):

```sh
IMAGE=ghcr.io/nhestrompia/proofci-toolchain:v0.1.0
OPTS="--security-opt seccomp=unconfined --security-opt apparmor=unconfined --security-opt systempaths=unconfined"
docker run --rm $OPTS -v "$PWD:/repo:ro" -v "$PWD/.proofci-vendor:/vendor" \
  $IMAGE fetch --base /repo --head /repo --out /vendor
```

Add `.proofci-vendor/` to `.gitignore`.

Create `proofci/Contract.lean` with only an import for now:

```lean
import Bank            -- the crate name in UpperCamelCase
```

Then run `dev`. It translates the crate and keeps the result in a Docker
volume:

```sh
docker run --rm --network none $OPTS -v "$PWD:/repo:ro" -v "$PWD/.proofci-vendor:/vendor:ro" \
  -v proofci-dev:/tmp/proofci-dev $IMAGE dev --repo /repo --vendor /vendor
```

To read the generated Lean, run
`docker run --rm -v proofci-dev:/w alpine cat /w/lean/Bank.lean`. Each Rust
function becomes a Lean `def` returning `Result`. A panic or an overflow is a
failed `Result`.

## 4. Write the contract

`proofci/Contract.lean` states each guarantee. Every statement ends in
`sorry`, because the proofs live elsewhere.

```lean
import Bank
open Aeneas Aeneas.Std Result bank

/-- Withdrawing more than the balance is rejected. -/
theorem withdraw_rejects_overdraft (balance amount : Std.U64) (h : balance.val < amount.val) :
    withdraw balance amount = ok none := by sorry

/-- Otherwise the new balance is exactly the difference (and nothing panics). -/
theorem withdraw_exact (balance amount : Std.U64) (h : amount.val ≤ balance.val) :
    withdraw balance amount ⦃ r => ∃ b, r = some b ∧ b.val = balance.val - amount.val ⦄ := by sorry
```

`f x ⦃ r => P r ⦄` means "the call succeeds (no panic, no overflow) and its
result satisfies `P`". `f x ⦃ _ => True ⦄` on its own is the guarantee
"never panics or overflows".

The contract is the part people must review: ProofCI checks that proofs match
it exactly, not that it says the right thing. It does flag statements that
cannot constrain the code:

- the function appears only in a hypothesis
- a hypothesis assumes the result
- the conclusion is trivially true

## 5. Write the proofs

`proofci/Proofs.lean` restates each theorem exactly and proves it. Run `dev`
after each edit; it prints Lean's errors and unsolved goals in a few seconds:

```lean
import Bank
import ProofciSpecs     -- extra step lemmas shipped with ProofCI (optional)
open Aeneas Aeneas.Std Result bank

theorem withdraw_rejects_overdraft (balance amount : Std.U64) (h : balance.val < amount.val) :
    withdraw balance amount = ok none := by
  unfold withdraw
  rw [if_pos (by scalar_tac)]   -- `amount > balance` holds, so take the first branch

theorem withdraw_exact (balance amount : Std.U64) (h : amount.val ≤ balance.val) :
    withdraw balance amount ⦃ r => ∃ b, r = some b ∧ b.val = balance.val - amount.val ⦄ := by
  unfold withdraw
  step*
```

Coding agents are good at this loop: give them the contract, the generated
Lean, [writing proofs](writing-proofs.md) and the `dev` command.

When the proofs build, run the final check (`--judge`) or the exact CI
command:

```sh
docker run --rm --network none $OPTS -v "$PWD:/base:ro" -v "$PWD:/head:ro" \
  -v "$PWD/.proofci-vendor:/vendor:ro" $IMAGE check --base /base --head /head --vendor /vendor
```

## 6. Add the workflow and make it required

`.github/workflows/proofci.yml`, committed to the default branch:

```yaml
name: ProofCI
on:
  pull_request_target:
    types: [opened, synchronize, reopened]
  merge_group:
  push:
    branches: [main]
permissions:
  contents: read
  pull-requests: read
jobs:
  proofci:
    runs-on: ubuntu-latest
    timeout-minutes: 30
    steps:
      - uses: nhestrompia/proofci@v0.1.0
        with:
          path: .
```

Then, in the repository settings, add `ProofCI / proofci` as a required status
check in branch protection (or a ruleset). Without that, a failing check is
only advice.

Use `pull_request_target`, not `pull_request`. Under `pull_request` a pull
request can edit the workflow that judges it. ProofCI warns if you get this
wrong.

## 7. What a pull request then sees

| Change | Result |
|---|---|
| Code still satisfies the guarantees and the proofs still check | ✅ passed |
| Proofs need updating after a refactor | ❌ `unproven`, with Lean's error; update `Proofs.lean` in the same PR |
| Code breaks a guarantee | ❌ `unproven`; no proof can exist |
| Signature changed so the contract no longer type-checks | ⚠️ `contract-stale`; a maintainer updates the contract (a policy change) |
| Code reaches something ProofCI cannot translate | ⛔ `unsupported`, with the source line |
| Guarantee removed or contract weakened | blocked until an approver approves that exact commit |

See [the demo repository](https://github.com/nhestrompia/proofci-demo/pulls)
for live examples.
