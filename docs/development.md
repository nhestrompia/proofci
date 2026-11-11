# Development

## Build and test

```sh
docker buildx build -f toolchain/Dockerfile -t proofci-toolchain:dev --load .
docker run --rm --network none \
  --security-opt seccomp=unconfined --security-opt apparmor=unconfined --security-opt systempaths=unconfined \
  -v "$PWD:/src:ro" -w /src -e PYTHONPATH=/src \
  --entrypoint python3 proofci-toolchain:dev -m tests.run_scenarios --jobs 4
```

Building the image from scratch takes about 17 minutes.

The unit tests need no toolchain (`tests.test_typescript_deps` replaces the sandbox and
the package managers with fakes), so they also run with plain `python3 -m unittest
discover -s tests -t .` where PyYAML is installed. The translator's own tests are
`node --test typescript/translate.test.mjs`. `tests.test_examples` installs the
packages of `examples/ts-packages` and is skipped when the npm registry can't be reached.

## Bridge fixtures

`spike/core` holds the experiment that ties the Lean view of a TypeScript function to a
model of JavaScript. A new form the translator accepts needs a fixture there as well:
add a function to [`fixtures/gaps/gaps.ts`](../spike/core/fixtures/gaps/gaps.ts) and its
name to [`corpus-gaps.tsv`](../spike/core/corpus-gaps.tsv), then generate the bridges and
check each file with Lean inside the toolchain image:

```sh
cd spike/core && mkdir -p /tmp/gaps
CORPUS=$PWD/fixtures node bridge3.mjs corpus-gaps.tsv /tmp/gaps
# then, in the image with the spike's .lake volume: lake env lean /tmp/gaps/F0.lean
```

A bridge that proves must print only the standard axioms. `mutate.py` plants wrong
translations in proved files, and every one must fail to check.

## Toolchain

[`toolchain/Dockerfile`](../toolchain/Dockerfile) pins every component by
version and SHA-256:

- Lean 4.35.0
- Mathlib v4.35.0
- Aeneas nightly-2026.11.02
- Charon at the commit Aeneas pins
- Rust nightly-2026-09-17
- Node 24.19.0 with the TypeScript compiler (`typescript/package-lock.json`), its own npm,
  and pnpm and Yarn 1 pinned by `toolchain/package-managers/package-lock.json`. The
  package managers only install a TypeScript project's packages; see
  [packages](typescript.md#packages)

Mathlib is pruned to the modules Aeneas imports. The image is 1.7 GB compressed
and built for Linux x86_64 and arm64.

The image has two parts:

- **Toolchain base** (`--target toolchain`): Rust, Charon, Lean, Mathlib and Aeneas. It changes only when a pin in `toolchain/` changes, and `main` publishes it under a hash of `toolchain/`.
- **Release image** ([`toolchain/Release.Dockerfile`](../toolchain/Release.Dockerfile)): adds ProofCI's code on top in seconds.

When Aeneas or Lean changes, regenerate `typescript/lean-tokens.json` from
`Lean.Parser.getTokenTable`, keeping the identifier-shaped entries. Generated code
puts `«»` around those words, so a field called `name` still compiles.

## CI

Pull requests that leave `toolchain/` alone pull the published base and run the
scenarios as 5 parallel shards per architecture. Pull requests that change a pin
rebuild the base, which takes about 20 minutes.

`main` publishes a multi-arch image for each commit and signs its build
provenance. Pushing a `vX.Y.Z` tag on a commit gives that commit's image the
version tag; nothing is rebuilt.

## Scenarios

[`tests/test_scenarios.py`](../tests/test_scenarios.py) runs the real toolchain
against adversarial changes to the example and checks every resulting status:

- **Wrong code:** a buggy fee, an overflowing transfer, a renamed function, a changed signature, a call into a library function with no model
- **Fake proofs:** `sorry`, a weakened statement, a fake model of the code, a committed fake translation, an extra `axiom`, `native_decide`, a theorem added with kernel checking switched off, citing the contract's own `sorry`
- **Attacks on the checker:** proof code that writes to the contract and model sources, or recompiles a weaker contract during the build; a dependency whose build script rewrites the code under test
- **Policy and contracts:** a weakened policy, statements that assume their result or constrain nothing
- **Scope:** `unsafe` code inside and outside the verified functions, a new dependency, a workspace member, a broken import

[`tests/test_models.py`](../tests/test_models.py) compares the standard-library
models with `rustc`.
