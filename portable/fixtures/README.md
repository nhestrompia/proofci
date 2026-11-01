# Example reports

These files record real runs of `test_cli_linux.py`. Each combines the
versioned envelope, protected baseline, and report for inspection. The Git
commit IDs identify the temporary fixture repository created by the test.
Run the test to create a fresh repository and reproduce the outcomes.

`passing.json` includes a verified required obligation and a missing advisory
one. `obsolete.json` records a changed candidate with the old proof bundle.

`github-normalized.json` records the local pinned-image results for the three
GitHub example scenarios. `test_github_example_linux.py` compares decisions,
reasons, evidence digests, gate status and exit codes against this reference.
