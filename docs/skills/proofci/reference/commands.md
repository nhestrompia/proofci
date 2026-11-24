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
# List which exported functions translate; each refusal has reason + hint.
python3 -P -m proofci scan --repo <dir> [--package <subdir>] [--vendor <dir>]
# WARNING: exits 2 on the first unsupported construct in a package — on real
# code, pick candidates by reading source, confirm each with dev --show.

# Fast iteration: translate + typecheck the contract, print Lean errors.
python3 -P -m proofci dev --repo <dir> --json      # errors may be truncated
python3 -P -m proofci dev --repo <dir> --show      # full Lean errors + the view

# The real CI check, in the toolchain image. Run on the HOST from the ProofCI
# checkout (it needs action/seccomp.json and shells out to docker).
cd $CHECKOUT
python3 -P -m proofci local --repo <dir> --image proofci-toolchain:dev --base HEAD
```

**Temporary workaround — `--base HEAD`**: `local` reads `proofci.yaml` from the
base ref (merge-base with the remote default branch), which does not exist on a
first adoption — without it you get `proofci.yaml not found in /base`, exit 2.
It will be replaced by a first-adoption mode (work in progress); `--policy head`
does NOT fix it.

Gotchas from the pilots:

- `proofci local` must run on the host (it calls `docker`), from the checkout.
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
6. **Run `local --base HEAD`** and read the report.
7. **Try to break it**: flip a comparison in the source; the check must block.
8. Commit `proofci.yaml`, `proofci/Contract.lean`, `proofci/Proofs.lean`,
   the code refactors, and `proofci/gaps.jsonl`.
