# GitHub Actions source-head example

This example runs the portable CLI on a pull request's source commit. It records
the pull request number, head, base and `source-head-only` scope alongside the
CLI report. It does not validate GitHub's synthetic merge commit. The workflow
job fails when preparation or verification fails; the artifact upload runs even
when verification exits 1 or 2. The report contains evidence references and
digests, not a complete evidence archive. If setup fails before the CLI starts,
there may be no report.

This is an example for a dedicated, disposable Linux ARM64 runner. It has not
been exercised in a live GitHub Actions run in this repository. Do not treat it
as an established required check or a substitute for the hosted service's
head-freshness and publication controls. `pull_request_target` runs with the
base workflow and its job is associated with the base context; configure and
validate any branch protection separately. The checked-out pull request is
untrusted data: never run its scripts, actions, build steps or configuration on
the runner. Do not give the job secrets or write permissions.

## Provisioning

1. On the isolated runner, install Docker, Python and Git, and install this exact
   verifier checkout at `/opt/proofci`. Protect it from repository writers and
   from the runner's unprivileged account. Build and load the local-only pinned
   image as described in [portable verification](../../portable/README.md).
   The launcher checks the image ID. No public image distribution is authorized.
2. Place the approved `baseline.json` and its contract files under
   `/opt/proofci-baseline`, outside the checkout. Protect that directory and
   its parent from repository writers and from the runner account. The runner
   needs read access. Select or update the baseline through a maintainer-owned
   process, not from pull request content. The example uses one fixed baseline;
   it does not automatically switch baselines when the base branch changes.
3. Register an isolated runner with the `proofci-isolated` label and restrict
   it to trusted repositories. Recreate it between jobs. Docker and the host are
   trusted by the local CLI; a general shared self-hosted runner is unsuitable.
4. Copy `proofci.yml` into `.github/workflows/` on the protected default branch.
   Keep the workflow and installed verifier under maintainer control. A workflow
   submitted in a pull request is not the trusted configuration.

The checkout action uses the read-only `GITHUB_TOKEN` to fetch the target
repository and does not persist it in Git configuration. Fork pull requests
supply a source commit through GitHub's pull request ref; the token must be able
to read that commit. Organization policies, private forks, runner access and
approval settings can prevent a run. Do not grant fork code credentials to
work around those limits. The base commit must be present in the full checkout;
preparation fails if either commit cannot be verified.

The artifacts inherit the repository's Actions access and retention settings.
Review those settings before using private source or contracts. An artifact is
not an authenticated baseline and must not be used to select one. For a replay
bundle, follow the separate export instructions in the portable README.
