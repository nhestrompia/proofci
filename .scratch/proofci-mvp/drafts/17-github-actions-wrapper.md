# 17: Run the verifier in an unprivileged GitHub Actions job

**What to build:** A repository runs the pinned CLI in Actions and retains its report, evidence, and blocking exit result without creating a second verification engine.

**Blocked by:** 05: Verify every approved obligation through a portable CLI.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/17

- [ ] A real Actions job runs the pinned Linux distribution on passing, unproven, and execution-failure fixtures and preserves their normalized reports and exit codes.
- [ ] Available reports and evidence upload even when the verifier exits nonzero. The wrapper never converts a failed verifier into a successful required gate.
- [ ] Fork deterministic checking requires no model or publishing credentials and executes candidate code in an unprivileged PR context.
- [ ] The example never obtains secrets by executing candidate code in a privileged pull_request_target workflow. It records whether it checks a head or actual merge result.
- [ ] The guide uses a protected baseline and explains that an editable candidate workflow alone is not an authoritative gate. Queue-enabled examples include the appropriate merge-group trigger.
- [ ] Keep the wrapper thin. Later property-result additions flow through the public CLI interface without wrapper-specific verification rules.

**Agent ownership:** Own Actions packaging, examples, and platform-specific acceptance. Do not modify CLI semantics or depend on the native App.

**Spec coverage:** user stories 2, 24, 37, 39, 40.
