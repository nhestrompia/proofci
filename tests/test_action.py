"""Policy-change approval rules in action/run.py (GitHub API mocked)."""

import io
import json
import os
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "action"))

import run  # noqa: E402

HEAD = "a" * 40


def review(login, state="APPROVED", commit=HEAD, association="COLLABORATOR"):
    return {"user": {"login": login}, "state": state, "commit_id": commit, "author_association": association}


class ApprovalTests(unittest.TestCase):
    def approved(self, reviews, approvers=None, author="author"):
        env = {"PR_NUMBER": "7", "GH_TOKEN": "t", "API_URL": "https://api.github.test",
               "REPOSITORY": "o/r", "PR_AUTHOR": author}
        body = io.BytesIO(json.dumps(reviews).encode())
        with mock.patch.dict(os.environ, env), \
                mock.patch.object(run.urllib.request, "urlopen", return_value=mock.MagicMock(
                    __enter__=lambda s: body, __exit__=lambda *a: False)):
            return run.approved_on(HEAD, approvers)

    def test_default_any_collaborator_but_the_author(self):
        self.assertEqual(self.approved([review("carol")]), "carol")
        self.assertIsNone(self.approved([review("author")]))
        self.assertIsNone(self.approved([review("drive-by", association="CONTRIBUTOR")]))

    def test_approval_must_be_on_the_exact_commit(self):
        self.assertIsNone(self.approved([review("carol", commit="b" * 40)]))

    def test_latest_decision_wins(self):
        self.assertIsNone(self.approved([review("carol"), review("carol", state="CHANGES_REQUESTED")]))

    def test_designated_approvers(self):
        self.assertIsNone(self.approved([review("carol")], approvers=["alice"]))
        self.assertEqual(self.approved([review("Alice", association="NONE")], approvers=["alice"]), "Alice")
        self.assertIsNone(self.approved([review("alice")], approvers=["alice"], author="alice"))

    def test_locked_policy(self):
        self.assertIsNone(self.approved([review("carol", association="OWNER")], approvers=[]))


if __name__ == "__main__":
    unittest.main()
