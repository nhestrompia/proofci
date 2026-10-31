# Lean source-binding spike

This spike checks a deliberately narrow question from [issue #1](https://github.com/nhestrompia/proofci/issues/1): can a trusted challenge refer to the admitted Lean candidate rather than an old or shadow definition? It does not establish correctness of arbitrary Lean, a compiled program, or a hosted verification service.

The recorded [binding decision](decision.md) is **go for this narrow research
subset**, subject to the trust assumptions below. It is not a production or
hosted-enforcement approval.

## Run

Provide a candidate and a contract from a trusted, approved baseline:

```lean
def target (x : Nat) : Nat := x + 1
```

```json
{"rhs":"x + 1"}
```

On a Docker host with Python 3, `curl`, `ar`, `tar`, and `zstd`, run:

```sh
experiments/source-binding/linux.sh candidate.lean contract.json
```

The runner downloads and checks the pinned Lean and bubblewrap archives, extracts a fresh toolchain, and starts the pinned ARM64 Linux image without networking. To reuse downloaded archives, set `PROOFCI_LEAN_ARCHIVE` and `PROOFCI_BWRAP_PACKAGE` to their paths. Their SHA-256 hashes are still checked. The image digest, package URLs and checksums, and container settings are fixed in `linux.sh`.

The JSON report identifies the input bytes, generated statements, candidate and challenge exports, dependency names, toolchain, checker and comparator result. A successful sandboxed check returns `verified` and exit status 0. Unsupported input, a failed proof, invalid evidence, or infrastructure failure returns `unproven` and a nonzero status; failure is not a proof of a violation. The report covers only this candidate and this contract. It does not establish that a human approved the contract. Protect the contract and the verifier from changes by the candidate being checked.

## Supported language and binding

The candidate is exactly one declaration `def target (x : Nat) : Nat := <expression>`. The body and contract `rhs` accept `x`, decimal natural literals of at most four digits, parentheses, `+`, and `*`. Multiplication binds more tightly than addition. The parser consumes the entire input and rejects imports, comments, other declarations, macros, instances, attributes, unknown names, and runtime replacements. The only type is Lean's `Nat` from the pinned `Init` distribution. The contract means `target x = <rhs>` for every `x : Nat`; it has no user-supplied helpers, assumptions, or proof.

The trusted adapter copies the exact admitted candidate bytes into a fresh Lean module. It also independently constructs an explicit `Nat.add`/`Nat.mul` expression from the parsed syntax and asks Lean to prove by `rfl` that the elaborated target equals that expression. Challenge and solution import the same candidate and identity theorem. The trusted challenge fixes the contract; the generated solution may prove it but cannot supply a new statement. Comparator checks both theorem statements and the identity proof; Lean's kernel and Nanoda check the exported solution, with only `propext`, `Quot.sound`, and `Classical.choice` permitted. The challenge's `sorry` is a placeholder and is not permitted in the solution.

The pinned exporter records the elaborated target and its dependencies. A second export starts at the contract alone, and must include the candidate definition. The adapter checks exported declaration names against `core-dependencies.json`, permits `sorryAx` only in the challenge, and rejects unexpected declaration and outer record shapes. This is a policy over the trusted exporter's output, not an independent parser or proof of the exporter's completeness. The full extracted Lean distribution is hashed and must match the pinned read-only distribution. Source hashes and Comparator acceptance by themselves would not establish the source-to-challenge link; the restricted parser, identity theorem, fixed challenge, and trusted toolchain are part of that argument.

## Reproduce the checks

```sh
experiments/source-binding/linux.sh --admission
experiments/source-binding/linux.sh --adversarial > adversarial.jsonl
experiments/source-binding/linux.sh --corpus > corpus.jsonl
python3 -m unittest discover -s experiments/source-binding -p 'test_*.py' -v
```

`admission.py` tests fail-closed candidate and contract parsing. `adversarial.py` attempts shadow implementations, a changed specification helper, a weaker theorem, a custom axiom, and `sorry`. `corpus.py` exercises the ten mathematically reviewed contracts in [contract-review.md](contract-review.md), each with correct, equivalent and defective candidates, plus precedence cases. The fixture review is not maintainer approval of an enforcing baseline.

`probe.py` preserves an earlier demonstration that Lean alone accepts a theorem about a separate shadow function. The earlier [Linux corpus report](evidence/linux-arm64-corpus.jsonl) predates the pinned sandbox and identity checks and is retained as historical evidence only.

Ticket 04 adds [`evidence.py`](evidence.py), which validates an unpacked proof
bundle against authoritative candidate and contract bytes. It reconstructs the
challenge, rejects forbidden solution dependencies, and uses fixed checker and
toolchain policy. See [`evidence-format.md`](evidence-format.md) for the bundle
format, permitted axioms, normalized reasons, and construction/replay boundary.

## Trust boundary

The caller must use a protected verifier and approved contract. The host, its kernel, Docker, the pinned image, archive verification, Lean exporter, Lean kernel, Nanoda, and the source adapter are trusted. The read-only bind mount assumes the host does not change its backing files while the run is active. Comparator's bubblewrap sandbox runs inside an unprivileged offline container; Docker's seccomp and system-path masks are relaxed to allow the nested user and mount namespaces. This experiment does not demonstrate the disposable-VM isolation required for hosted untrusted workloads. It also does not independently validate arbitrary reports or evidence bundles; a `verified` result comes from this run, not from importing a worker's self-reported JSON.
