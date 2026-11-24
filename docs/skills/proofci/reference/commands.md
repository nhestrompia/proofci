# Commands and the adoption loop

## Invocation

There is no installable `proofci` binary yet. Run it from a ProofCI checkout:

```sh
CHECKOUT=/path/to/proofci
PYTHONPATH=$CHECKOUT python3 -P -m proofci <command> ...
```

**Temporary invocation** — it exists only until `proofci` ships as a package.
`-P` matters meanwhile: a repo that has a `proofci/` contract directory would
otherwise shadow the package. On a host without `bwrap`, run everything inside
the toolchain image instead (see "In the image" below).

## What works today

```sh
# List which exported functions translate; each refusal has reason + hint +
# a stable `code`; `summary.by_code` counts them. Per-function: a refusal
# blocks only the functions that reach the construct. (exit 2 = fatal failure.)
python3 -P -m proofci scan --repo <dir> [--package <subdir>] [--vendor <dir>]

# Fast iteration: translate + typecheck the contract, print Lean errors.
python3 -P -m proofci dev --repo <dir> --json      # errors may be truncated
python3 -P -m proofci dev --repo <dir> --show      # full Lean errors + the view

# The real CI check, in the toolchain image. Runs on the host from anywhere
# (it shells out to docker); scan/dev still need bwrap on the host.
python3 -P -m proofci local --repo <dir> --image proofci-toolchain:dev
```

**First adoption**: when the base ref has no `proofci.yaml` at all, the run is
a first adoption — the candidate's manifest is used, every guarantee counts as
new, and the run is a policy change that blocks until a maintainer who is NOT
the pull-request author approves the contract. The new manifest's
`policy.approvers` isn't trusted yet; it takes effect once merged. `local`
reports `first_adoption: true` for this; no `--base` flag is needed.

`PROOFCI_*` tuning variables the check honours (`PROOFCI_BRIDGE_TIMEOUT`,
`PROOFCI_BRIDGE_BUDGET`, `PROOFCI_MUTATION_FULL`, `PROOFCI_MUTANTS`,
`PROOFCI_MUTATION_BUDGET`, `PROOFCI_PARALLEL_JUDGES`, `PROOFCI_NODE_HEAP`) pass
through to the container; no other environment is. `PROOFCI_NODE_HEAP` is a
number of megabytes (at most 16384) and becomes Node's `--max-old-space-size`
for the Node-comparison stage (large files can exceed the default ~4 GB heap);
it is the only Node flag the check accepts.

Gotchas from the pilots:

- `proofci local` needs `docker` on the host but no longer needs the checkout:
  it finds `seccomp.json` beside the package or at the image's install path.
- `proofci fetch --out <dir>`: the vendor dir must be OUTSIDE the repo or the
  copy recurses forever. `chmod 777` the dir.
- `--fetch` can't handle pnpm `link:` workspace deps; use a vendor dir.
- Only `local` takes `--image`. `scan`/`dev` on the host need `bwrap`.
- Manifest requires ≥1 guarantee per target — a target listed only to test
  translation must be dropped or given a guarantee.
- Targets must be `export const`/named exports to be compared with Node
  ("not exported" otherwise — still proved, just not differentially tested).

## In the image (no bwrap, or Lean iteration)

```sh
OPTS="--security-opt seccomp=unconfined --security-opt apparmor=unconfined --security-opt systempaths=unconfined"
docker run --rm --network none $OPTS -v "$PWD:/repo:ro" -v proofci-dev:/w \
  -w /w/lean -e PYTHONPATH=/opt/proofci --entrypoint python3 proofci-toolchain:dev -m proofci dev --repo /repo --show
```

`dev` on the host fails cryptically (`/opt/aeneas/...` missing) — that's
"run inside the image". Fastest proof loop (~10–20× faster than `dev`): copy
`proofci/Proofs.lean` + `Contract.lean` into the `proofci-dev` volume's lean dir
and run `lake env lean Proofs.lean` there.

## The loop

1. **Pick targets.** Pure functions that decide something a reviewer cares
   about: money, limits, parsing, permissions, ordering. Small named helpers
   (`isLeapYear`, `validateCode`) are ideal first targets. Skip async/Prisma
   handlers — extract their pure cores instead (see typescript-subset.md).
2. **Declare** in `proofci.yaml` (`targets` + `guarantees`).
3. **Check translation** with `dev --show` or `scan`. On `unsupported`, refactor
   the code, not the goal.
4. **State guarantees** in `proofci/Contract.lean` with `/--` doc comments,
   ending `:= by sorry`. Shapes: see contracts.md — the checker has opinions.
5. **Prove** in `proofci/Proofs.lean`; iterate with `dev` / `lake env lean`.
6. **Run `local`** and read the report. A first adoption reports
   `first_adoption: true` and blocks for maintainer approval in CI — locally
   you read the report as usual.
7. **Try to break it**: flip a comparison in the source; the check must block.
8. Commit `proofci.yaml`, `proofci/Contract.lean`, `proofci/Proofs.lean`,
   the code refactors, and `proofci/gaps.jsonl`.
