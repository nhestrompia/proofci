## What to build

A repository runs the pinned CLI in Actions and retains its report, evidence, and blocking exit result without creating a second verification engine.

## Acceptance criteria

- [ ] A real Actions job runs the pinned Linux distribution on passing, unproven, and execution-failure fixtures and preserves their normalized reports and exit codes.
- [ ] Available reports and evidence upload even when the verifier exits nonzero. The wrapper never converts a failed verifier into a successful required gate.
- [ ] Fork deterministic checking requires no model or publishing credentials and executes candidate code in an unprivileged PR context.
- [ ] The example never obtains secrets by executing candidate code in a privileged pull_request_target workflow. It records whether it checks a head or actual merge result.
- [ ] The guide uses a protected baseline and explains that an editable candidate workflow alone is not an authoritative gate. Queue-enabled examples include the appropriate merge-group trigger.
- [ ] Keep the wrapper thin. Later property-result additions flow through the public CLI interface without wrapper-specific verification rules.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/5

## Agent ownership

Own Actions packaging, examples, and platform-specific acceptance. Do not modify CLI semantics or depend on the native App.

## Specification coverage

Approved ProofCI MVP spec, user stories 2, 24, 37, 39, 40. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:17 -->
