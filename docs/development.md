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

## Toolchain

[`toolchain/Dockerfile`](../toolchain/Dockerfile) pins every component by
version and SHA-256:

- Lean 4.35.0
- Mathlib v4.35.0
- Aeneas nightly-2026.11.02
- Charon at the commit Aeneas pins
- Rust nightly-2026-09-17

Mathlib is pruned to the modules Aeneas imports. The image is 1.7 GB compressed
and built for Linux x86_64 and arm64.

The image has two parts:

- **Toolchain base** (`--target toolchain`): Rust, Charon, Lean, Mathlib and Aeneas. It changes only when a pin in `toolchain/` changes, and `main` publishes it under a hash of `toolchain/`.
- **Release image** ([`toolchain/Release.Dockerfile`](../toolchain/Release.Dockerfile)): adds ProofCI's code on top in seconds.

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
