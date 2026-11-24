"""First adoption: the base checkout has no proofci.yaml at all.

The candidate's manifest is used, every guarantee counts as new, and the run is
a policy change needing approval. Only a genuinely absent file counts: a
manifest that is a symlink, a directory or unreadable stays an error, and a
pull request that removes or renames an existing one is a policy change.
"""

import shutil
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from proofci import check as check_mod  # noqa: E402

MANIFEST = """\
version: 1
crate: .
lean: proofci

targets:
  - id: t
    function: ledger::calculate_fee
    guarantees:
      - id: g
        theorem: some_theorem
"""


def make_head(dest):
    (dest / "proofci.yaml").write_text(MANIFEST)


class Adoption(unittest.TestCase):
    def check(self, make_base, make_head_fn=make_head):
        with tempfile.TemporaryDirectory() as tmp:
            base, head = Path(tmp) / "base", Path(tmp) / "head"
            base.mkdir()
            head.mkdir()
            make_base(base)
            make_head_fn(head)
            return check_mod.check(base, head)

    def test_first_adoption_uses_the_candidate_manifest(self):
        report = self.check(lambda base: None)
        self.assertTrue(report.first_adoption)
        self.assertTrue(report.policy_changes)
        self.assertIn("first adoption", report.policy_changes[0])
        self.assertFalse(report.passed)  # blocks until the contract is approved

    def test_first_adoption_still_blocks_without_proofs(self):
        report = self.check(lambda base: None)
        statuses = {o.status for o in report.outcomes}
        self.assertFalse(statuses & {"verified"})

    def test_missing_candidate_manifest_in_adoption_errors(self):
        with self.assertRaises(check_mod.ConfigError):
            self.check(lambda base: None, lambda head: None)

    def test_a_symlinked_base_manifest_is_not_an_adoption(self):
        def base_with_symlink(base):
            (base / "proofci.yaml").symlink_to("/nonexistent-target")
        with self.assertRaises(check_mod.ConfigError):
            self.check(base_with_symlink)

    def test_a_manifest_directory_is_not_an_adoption(self):
        def base_with_dir(base):
            (base / "proofci.yaml").mkdir()
        with self.assertRaises(check_mod.ConfigError):
            self.check(base_with_dir)

    def test_removing_the_manifest_is_a_policy_change_not_an_adoption(self):
        with tempfile.TemporaryDirectory() as tmp:
            base, head = Path(tmp) / "base", Path(tmp) / "head"
            base.mkdir()
            make_head(base)
            head.mkdir()
            report = check_mod.check(base, head)
        self.assertFalse(report.first_adoption)
        self.assertTrue(report.policy_changes)
        self.assertIn("removed", report.policy_changes[0])

    def test_a_symlinked_candidate_manifest_is_not_an_adoption(self):
        def head_with_symlink(head):
            (head / "proofci.yaml").symlink_to("/etc/passwd")
        report = self.check(make_head, head_with_symlink)
        self.assertFalse(report.first_adoption)
        self.assertIn("removed or is invalid", report.policy_changes[0])

    def test_fetch_on_first_adoption_reads_the_candidate_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            base, head, vendor = Path(tmp) / "base", Path(tmp) / "head", Path(tmp) / "vendor"
            base.mkdir()
            head.mkdir()
            make_head(head)
            # A Rust crate with no registry deps stages nothing; the point is
            # that fetch resolves the head manifest instead of failing on /base.
            try:
                check_mod.fetch(base, head, vendor)
            except check_mod.extract.Unsupported:
                pass  # the manifest was found; the (fake) crate itself can't stage


if __name__ == "__main__":
    unittest.main()
