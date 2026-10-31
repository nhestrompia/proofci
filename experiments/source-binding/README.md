# Source-binding probe

This is an initial experiment for [issue #1](https://github.com/nhestrompia/proofci/issues/1), not a verifier. It checks three small Lean files with Lean 4.35.0:

1. A contract proof for the original function succeeds.
2. The same proof fails after the function changes from adding one to adding two.
3. A theorem about a separately declared shadow function succeeds even though the candidate still adds two.

Run `LEAN=/path/to/lean python3 experiments/source-binding/probe.py`. The script exits successfully only if all three observed compiler results match these expectations. It emits hashes of the source and contract and Lean's version. The shadow case deliberately succeeds: rejecting it requires the trusted binding mechanism that this probe does not implement. The candidate source hashes identify input bytes but do not prove which definition a theorem refers to. Similarly, comparing a solution to a challenge would only help if the challenge were already bound to the candidate.

The current decision is **no-go** for source-verified claims. The adapter below is a further experiment; it does not establish a complete semantic dependency closure or the reviewed corpus required by the ticket. A passing experiment is not proof that the adapter is sound.

## Experimental adapter

`binding.py` accepts a candidate file and a separate trusted JSON contract. The candidate must contain exactly one declaration of this form:

```lean
def target (x : Nat) : Nat := x + 1
```

The body and the contract's `rhs` field may contain only `x`, decimal natural literals of at most four digits, parentheses, `+`, and `*`. The tokenizer and recursive-descent parser consume the entire input; declarations, imports, comments, macros, instances, attributes, and references to any other name are rejected. The only type is Lean's `Nat` from the pinned toolchain's implicit `Init` import. This is intentionally much narrower than general Lean. The trusted contract statement is `target x = <rhs>` and has no user-provided helpers, assumptions, notation or proof. The adapter copies the exact admitted candidate bytes into `Candidate.lean`, imports it into both challenge and solution, and constructs the theorem and fixed proof itself.

The script invokes Lean 4.35.0's Lake Comparator with the `propext`, `Quot.sound`, and `Classical.choice` axioms permitted and Nanoda as an external checker. It records input, generated statement and supplied executable hashes and the comparator output. It requires the supplied Lean and Lake executables to share a directory and checks the version resolved by `lake env lean`. The candidate hash identifies source bytes, not an elaborated definition. The version check does not independently establish which binary Lake used, and the script does **not** identify the full semantic dependency closure or verify that all toolchain files match their advertised version. The caller supplies the paths to the toolchain, so they must come from a trusted installation. Lake's own sandbox is disabled for this experiment. Run it only in a disposable isolated environment with no credentials or network. The adapter always reports `unproven` and exits 1, including when Comparator accepts; `comparator_exit` is an experimental observation, not an authoritative result.

For example, in such an environment:

```sh
printf 'def target (x : Nat) : Nat := x + 1\n' > candidate.lean
printf '{"rhs":"x + 1"}\n' > contract.json
python3 experiments/source-binding/binding.py candidate.lean contract.json \
  --lean /path/to/lean/bin/lean --lake /path/to/lean/bin/lake
```

`admission.py` probes several rejected candidate and contract inputs at the CLI boundary, with a valid positive control. `corpus.py` tries ten arithmetic statements against base, equivalent and defective variants. An independent review checked the equations and counterexamples, but they are not maintainer-approved contracts and do not satisfy the ticket's reviewed-corpus requirement. Each script accepts the same `--lean` and `--lake` arguments and exits 0 only when its observations match expectations. The corpus emits full Comparator reports as JSON lines.

The remaining work includes an independently reviewed adapter and dependency closure, a broader reviewed mutation corpus including misleading specification dependencies, and a fully pinned and isolated Linux acceptance run. Comparator acceptance alone does not show that this adapter bound the intended source; the admission and construction logic must be audited and tested independently.

## Observed Linux run

On 2026-10-31, the probe returned exit status 0 in a fresh ARM64 container, with networking disabled. Lean accepted the base and shadow cases; the changed candidate failed with `error: unsolved goals`. This is a reproduction of this probe only, not the ticket's full acceptance run.

- Python image: `python@sha256:2d44738ebf4ce5f63b9d9ea871e9c7cfdc0426f7b0c97cac915fd88ded1d86bb`
- Lean archive: `lean-4.35.0-linux_aarch64.tar.zst`, SHA-256 `c8f0f8a3920e839718b1343e6781fd80a3e9b1024fbcd7078eb30f54e806b028`
- Lean reports commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The separate adapter base case also ran on ARM64 Linux with the same Lean archive, an isolated container based on `python@sha256:6a9220edda062e9223ea0784740a535987299420b96fbfd520b89bbd3e772485`, and networking disabled. Comparator returned 0 and both Nanoda and Lean's kernel accepted the solution. This does not establish sandbox safety or complete ticket acceptance.

The [Linux corpus report](evidence/linux-arm64-corpus.jsonl) records 30 observations from the same image and Lean archive: all 20 base and equivalent cases were accepted, and all 10 defective cases failed with the expected proof diagnostic. These results are observations about the restricted experiment, not a binding go decision.

To reproduce the adapter corpus after downloading and extracting the Lean archive as described below, use the Git-enabled Python image:

```sh
docker run --rm --network none --platform linux/arm64 --cap-drop ALL \
  --security-opt no-new-privileges --read-only --tmpfs /tmp:rw,size=2g \
  -v "$PWD/lean-4.35.0-linux_aarch64:/lean:ro" \
  -v "$REPO/experiments/source-binding:/probe:ro" \
  python@sha256:6a9220edda062e9223ea0784740a535987299420b96fbfd520b89bbd3e772485 \
  python3 /probe/corpus.py --lean /lean/bin/lean --lake /lean/bin/lake
```

Replace `corpus.py` with `admission.py` to run the admission checks. The container restricts this experiment, but it is not the disposable VM or independent validation environment required for a production trust boundary.

On an ARM64 Linux host with Docker, Python and `zstd` installed, run from a temporary directory, substituting the absolute repository path for `REPO`:

```sh
curl -fL https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux_aarch64.tar.zst -o lean.tar.zst
echo 'c8f0f8a3920e839718b1343e6781fd80a3e9b1024fbcd7078eb30f54e806b028  lean.tar.zst' | sha256sum -c -
tar --zstd -xf lean.tar.zst
docker run --rm --network none --platform linux/arm64 \
  -v "$PWD/lean-4.35.0-linux_aarch64:/lean:ro" \
  -v "$REPO/experiments/source-binding:/probe:ro" \
  -e LEAN=/lean/bin/lean \
  python@sha256:2d44738ebf4ce5f63b9d9ea871e9c7cfdc0426f7b0c97cac915fd88ded1d86bb \
  python3 /probe/probe.py
```
