# Ticket 19 live repository exercise

The exercise used `nhestrompia/proofci` and the branch
`proofci-ticket19-demo-f805eec2`. It used an isolated copy of the existing pilot
baseline store. The pilot's active store was not modified. A local trusted caller
checked the signed-in GitHub user's current repository permissions through the
GitHub API. This exercise did not use the hosted OAuth session or GitHub App
installation path.

The first candidate at `7d33ff9c3f1651609ea43ee913df1177341eb4b2` exhausted
the fixed 120-second obligation budget. The verifier returned `blocked`, and the copied baseline remained active. See
[the blocked report](budget-exhausted-report.json).

The replacement candidate at `d9c6545778fb4900d17d1fc07b4582150df31a1b`
replaced the `increment` contract with `increment-v2`. The run passed the
isolated worker and independent final validation. The migration activated in
the copied store. The report records the policy change, the removed `increment`
guarantee, and the added `increment-v2` guarantee. See [the migration report](migration-report.json) and
[the summary](migration-summary.json).

This exercise does not close the race between the last GitHub access and head
checks and the local activation transaction. It does not establish GitHub check
publication or merge enforcement.

The [blocked store snapshot](blocked-store.json) and [activated store snapshot](activated-store.json)
record the local SQLite state. The [migration script](migration-command.txt)
and [stale-approval script](stale-command.txt) record the commands used. These
scripts contain host-specific paths and modify the test branch. They are
execution records, not reusable setup scripts.

For the stale-approval exercise, the caller obtained a new authorization at
`7ba2ad047f7730d37c6c88c63a20f05b90dc0161` and verified that candidate. A
later commit advanced the branch to `fa2a4ca8d6ed54dbadfa6424ee0b4566fc454dd8`.
The activation operation rejected the new head, and the copied active baseline
remained unchanged. See [the stale summary](stale-summary.json),
[the verification report](stale-verification.json), and the verified record in
[the store snapshot](activated-store.json). A separate [recheck](stale-recheck.json)
recorded the rejection reason. Its [script](stale-recheck-command.txt) uses the
verified authorization and the advanced head.

On the later authority exercise, the local gateway advanced the same demo branch
from `fa2a4ca8d6ed54dbadfa6424ee0b4566fc454dd8` to
`aed0af69c803f3788681156aa0ee2b0add5144ed`. The exercise used a copied store
and the real isolated Lean verifier. After verification, authority revocation
and regrant invalidated the approval; the old baseline remained active. A new
approval was verified and activated. See [the result](authority-result.json)
and [the verifier report](authority-report.json). This replacement changed
policy but did not retire a guarantee. The earlier exercise above demonstrates
retirement. The demo branch did not have GitHub branch protection, so this
exercise does not demonstrate exclusive gateway enforcement or the hosted App
path.
