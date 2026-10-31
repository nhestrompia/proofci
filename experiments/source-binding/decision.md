# Binding decision

**2026-10-31: GO for the source-binding feasibility spike, limited to the
documented `Nat` expression grammar and the pinned Linux validator.** The
trusted caller must supply the approved contract and protect the verifier and
toolchain. This decision permits downstream work to use this adapter as an
experimental prerequisite. It is not approval to enforce a production merge
gate or a claim about arbitrary Lean, native code, or deployed behavior.

The decision rests on the following observed results and review:

- The [valid candidate](evidence/linux-good.json) returned `verified` with
  Comparator, Lean's kernel and Nanoda accepting the solution. The
  [defective candidate](evidence/linux-defective.json) returned `unproven`.
  Both reports identify the current adapter, runner, verdict code, pinned Lean
  distribution, generated statements, and candidate and challenge exports.
- The [pinned Linux corpus](evidence/linux-pinned-corpus.jsonl) recorded 32
  expected results: 21 successful base, equivalent or precedence cases and 11
  rejected defective cases. The ten obligations and their counterexamples were
  checked in an independent mathematical review, recorded in
  [contract-review.md](contract-review.md). This does not constitute
  maintainer approval of a baseline.
- The [admission run](evidence/linux-admission.jsonl) accepted its positive
  control and rejected ten unsupported inputs. The
  [adversarial run](evidence/linux-adversarial.jsonl) accepted its positive
  control and rejected six hostile solutions, including an identical shadow
  function, a different shadow function, a substituted specification helper,
  a weakened statement, a custom axiom and `sorry`.
- The source parser, canonical identity theorem, dependency-name policy,
  isolated runner and verdict boundary received separate standards and spec
  reviews. No concrete source-binding escape was found within the admitted
  language and stated trusted-environment assumptions.

The exporter, pinned toolchain, adapter, host and kernel remain trusted. The
dependency-name policy checks output from that trusted exporter; it is not an
independent proof that the exporter is complete. The Linux test uses an
offline container with Comparator's bubblewrap sandbox; it does not establish
the disposable-VM isolation or independent report ingestion required for a
hosted service. A no-go applies if these assumptions do not hold or if input
falls outside the supported grammar.
