# ProofCI verification feasibility

Research date: 31 October 2026. This note separates source-backed facts from proposed product decisions. The repository currently has a scaffold README and no verification implementation or established proof library.

## Assessment

ProofCI is feasible as a CI service that preserves explicit, reviewed formal contracts for a deliberately supported programming subset. The strongest first version checks Lean-native, pure, terminating functions and uses AI to repair proof bodies. A service that accepts arbitrary application code, invents its intended meaning, translates it with an LLM, and then advertises source-code correctness would lack the necessary semantic link. A theorem about a translated model proves the model's property; relating that model to the actual program is a separate obligation.

The engineering opportunity is useful even with this boundary: persist contracts, replay them for each exact revision, attempt bounded proof repair, and give developers reliable evidence of what was checked. The service should distinguish inability to prove from a demonstrated violation. This is a proposed scope, rather than a claim that an experiment in this repository has established practical success rates.

## What Lean establishes

Lean's kernel accepts a proof of a formal proposition relative to definitions and assumptions. The official manual distinguishes validity of the proof from the intended meaning of its statement, warns that tactics and imported meta-code can execute arbitrary actions, and treats unreviewed AI-generated proofs as potentially adversarial. It recommends stronger validation for that setting, including trusted challenge statements, isolated builds, statement comparison, and replay of exported proofs. A successful project build alone is insufficient evidence for ProofCI's promise. [Lean: Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)

Lean tracks transitive axiom dependencies. `sorry` and incomplete proofs rely on `sorryAx`; arbitrary axioms can assert false propositions. The usual mathematical foundation permits `propext`, `Classical.choice`, and `Quot.sound`. Native evaluation such as `native_decide` adds compiler-dependent axioms; current versions record individual computations rather than only the historical `Lean.trustCompiler` mechanism. [Lean: Axioms](https://lean-lang.org/doc/reference/latest/Axioms/)

Proposed acceptance policy:

- Allow only an explicit, versioned list of foundational axioms, initially those three standard axioms.
- Reject `sorryAx`, custom axioms, native-evaluation axioms, and proof-validation bypasses in accepted obligations, including dependencies.
- Derive this decision from checked declarations, not a text search for banned words. A library theorem can hide an incomplete dependency.
- Record exact Lean, library, checker, source, contract, and policy versions with each result.
- Label native evaluation as a different trust policy if introduced later; it must never silently receive the same guarantee.

`partial def` is logically opaque, whereas unsafe definitions cannot supply ordinary logical reasoning about their execution. Neither means that all Lean code importing an unsafe tactic implementation is logically invalid. Lean also provides `partial_fixpoint`, with different semantics and partial-correctness reasoning. Runtime replacement mechanisms such as `implemented_by` can substitute unsafe code without proving that substitution matches the logical definition. [Lean: Recursive Definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/)

For an MVP, accept target functions with safe, pure, total definitions; exclude target runtime replacements, FFI and user-supplied unsafe implementations. Keep proof tooling separate from target-program eligibility. A statement about a Lean function is a source-level logical guarantee. Running its compiled executable additionally trusts the compiler, runtime, platform, and any substituted implementation; ProofCI must describe that boundary rather than imply a verified binary.

## Connecting proofs to source

Three modes have materially different guarantees:

1. **Lean-native verification:** a theorem mentions the actual eligible Lean function from the checked revision. The proof and implementation share a formal language. This is the recommended first supported mode.
2. **Deterministic extraction:** a supported frontend regenerates a model from the exact foreign-language revision. Confidence also depends on the frontend's semantics, implementation, supported features, and external models. This is a credible expansion path, with those dependencies disclosed.
3. **AI or manual reimplementation:** someone writes Lean that resembles JavaScript, Python, Rust, or another program. Without an independently justified correspondence, the accepted proof establishes the Lean model only. This can assist specification development but must not receive a source-verified label.

Aeneas provides an existing route for Rust: Charon extracts an intermediate representation and Aeneas translates it to functional definitions with a Lean backend. Its current README targets a subset of safe Rust, lists remaining limitations, and explains that external definitions may need handwritten models. This is evidence of a usable specialized direction, not universal Rust coverage or a proof that every step of the implementation is verified. [Aeneas README](https://github.com/AeneasVerif/aeneas)

The original Aeneas paper supplies a semantic foundation for its functional translation and ownership-based reasoning. It does not justify treating arbitrary LLM-generated translations as equivalent. [Aeneas: Rust Verification by Functional Translation](https://arxiv.org/abs/2206.07185)

For a Rust spike, pin Rust, Charon, Aeneas, and Lean together; regenerate models inside the job; preserve extraction logs; enumerate supported constructs; and fail closed on unsupported extraction. Audit every external function model. Pay particular attention to integer overflow, panic/error behavior, aliasing, termination, and library operations. These are proposed acceptance checks. A Lean theorem over unbounded natural numbers must not be described as a theorem about wrapping machine integers without an explicit connection.

Verus is a useful alternative-backend precedent: it verifies specifications of a supported Rust subset using solver-based techniques. It is not a Lean backend and should have its own evidence and trust-policy identity if supported. [Verus README](https://github.com/verus-lang/verus)

## Persistent contracts and change analysis

The contract should consist of a stable identifier, reviewed formal proposition, target symbol, approved assumptions and models, and applicability scope. Natural-language text is supporting documentation. AI may propose the first formalization, but maintainers must decide that it captures the requirement. Logical validity cannot discover that an omitted authorization condition mattered to the product.

Preserve contracts from a trusted base revision. A PR that removes a theorem, renames its identifier, narrows its quantifiers, adds a stronger precondition, changes a supporting predicate, or changes verification policy must not make that obligation disappear. Report a contract-change request and verify existing obligations under the established policy. An explicit maintainer-approved contract revision can become the next baseline after merge.

Crucially, preservation means applying the established property to the **new implementation**, not accidentally replaying the old function body. The verifier must bind the trusted proposition to the eligible head definition and record that definition's identity. A challenge that continues importing base implementation code would produce irrelevant green results.

The proposed v0 binding mechanism is a restricted input language: allow pure total declarations, approved target types, and locked allowlisted imports; reject repository-defined commands, elaborators, macros, instances, custom coercions, initialization code, plugins, build hooks, and runtime substitutions in the target input. A trusted harness constructs the build configuration and challenge from base contracts plus admitted head declarations. Both the challenge and solution must reference the same checked head definitions. Compare their elaborated statements and complete semantic dependency closure, including helper bodies and resolved instances; names or source hashes alone are insufficient. Candidate proof code cannot replace any of those declarations.

This restriction needs a real parser and declaration-level validation, not a regular-expression filter. Its design remains a feasibility unknown: the spike must show that trusted elaboration plus exported declarations bind the admitted source to the exact constants being proved, and that the installed Comparator supports the required dependency checks. Comparator validates what it receives; it does not decide that a source-to-challenge adapter chose the intended implementation. Reject any input outside the admitted subset. If this binding cannot be demonstrated, do not ship the source-verified label.

Use the diff to explain and prioritize work, not decide correctness by itself. Start by replaying all registered obligations. Later, build conservative dependency closure over formal declarations and frontend dependencies; when a dependency is uncertain, recheck. An LLM's claim that a changed module is unrelated must never be the reason a required property is skipped.

## AI's role and the verification boundary

Lean Copilot demonstrates tactic suggestion, premise selection, and proof search with local or hosted models. This is evidence that model-assisted proof construction is practical tooling, not evidence that arbitrary software obligations can be solved automatically within CI budgets. [Lean Copilot](https://github.com/lean-dojo/LeanCopilot)

Use an interchangeable prover interface that receives a fixed obligation and permitted context and returns a candidate proof plus resource usage. Give the agent compiler feedback and a bounded attempt budget. It may edit proof bodies in an isolated workspace, but cannot redefine contract predicates, alter the target implementation, add assumptions, switch toolchains, or amend acceptance policy. Recheck the final candidate independently after the search process ends.

The current Comparator project records that its functionality moved into Lean core in v4.35.0 as `lake comparator` and `lake check`; the standalone repository is deprecated. [Comparator README and deprecation](https://github.com/leanprover/comparator) The core documentation describes challenge comparison, axiom restrictions, exported-proof checks, optional additional checkers, and sandbox configuration. Use that current interface rather than copying an archived setup. [Lake: Challenges and External Checkers](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator)

Similarly, standalone `lean4checker` moved into Lean as `leanchecker` starting in v4.28.0. `lake env leanchecker --fresh` replays declarations into a fresh kernel environment; it is a useful check, not a substitute for trusted statement comparison or an independently implemented checker. [lean4checker migration notice](https://github.com/leanprover/lean4checker)

For ProofCI, use pinned, tested core tooling behind a verifier adapter. Establish the trusted challenge before handling agent output. Run repository builds, elaboration, extraction, and proof search without publishing credentials in disposable workers. Keep the control plane, report signer, and contract store outside that worker. Do not load artifacts produced by an untrusted job into a privileged process merely because they have a Lean file extension. Validate the chosen checker and sandbox combination during the feasibility spike; this note does not certify it.

## Results that developers can interpret

Proposed property outcomes:

- **Verified:** the exact approved statement about the identified head implementation has an accepted proof under the declared policy.
- **Violated:** a checked refutation or a concrete counterexample validated against the property's semantics demonstrates failure. Preserve the witness and its validation method. Ordinary test failure should be labelled as executable evidence when it lacks a formal correspondence.
- **Unproven:** a proof attempt fails, exceeds its budget, or requires work outside the supported subset. Include the reason and actionable diagnostics.

Track infrastructure failure, cancellation, stale revision, and contract-policy rejection separately as run conditions. A tactic failure is not a counterexample; a proof-search timeout does not imply a false theorem. Make merge policy configurable, with required verified obligations failing closed when missing or unproven. Never report that an entire PR is correct solely because its registered properties were proved.

## Bounded MVP and experiments

Build one platform-independent command that verifies every registered contract for an exact checkout and emits a structured report. Integrate that command with GitHub after its semantics are demonstrable. Initially support Linux workers, a single pinned Lean toolchain, a reviewed import set, pure total targets, manual contract registration, replay, optional bounded AI proof repair, and the three property outcomes. Include a small example library with arithmetic, list transformations, and a state-transition function. Keep foreign-language extraction experimental and prominently scoped.

Proposed go/no-go evidence:

1. **Correctness:** create at least ten reviewed contracts with benign refactorings and deliberate defects. Every compatible refactoring must replay; every introduced defect must avoid a verified result. A subset with explicit checked counterexamples must report violated.
2. **Persistence:** demonstrate that deleting or weakening a contract, changing a hidden predicate, and omitting an obligation from output cannot make an existing requirement green.
3. **Trust and binding:** attempt direct and transitive `sorry`, custom axioms, native evaluation, target substitution, fake artifact reuse, theorem-name shadowing, misleading notation, instance changes, and helper-body replacement. A valid proof about the base implementation must fail when the head implementation violates the contract. The verifier must reject each attack and preserve the trusted challenge.
4. **Execution isolation:** demonstrate that build scripts and proof code cannot read report credentials, mutate trusted statements, or publish results. Unsupported sandbox/checker combinations block release.
5. **Reproducibility:** reconstruct an accepted report from recorded versions and revision. Never reuse a cached result after changing any semantic input.
6. **Cost:** measure cold setup, warm replay, AI success rate, tokens, and wall time over the fixture set. The implementation spec sets initial budgets of 120 seconds per obligation and 15 minutes per run. These are controls to test, not measured performance claims. Its larger pilot corpus extends the ten-contract trust spike.

Proceed with the Lean-native product if independent exported-proof validation, source binding, trust, and persistence checks pass and replay is operationally useful. Proceed with Rust support only after deterministic extraction, external-model accounting, and mutations demonstrate the intended source linkage. If meaningful onboarding still requires extensive proof engineering, position ProofCI first for teams already maintaining formal specifications rather than promise turnkey verification of general application repositories. These are research recommendations: no Lean execution or verification prototype was performed for this note.
