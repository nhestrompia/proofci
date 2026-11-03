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


class FakeResponse(io.BytesIO):
    def __init__(self, items, next_url=None):
        super().__init__(json.dumps(items).encode())
        self.headers = {"Link": f'<{next_url}>; rel="next"'} if next_url else {}

    def __enter__(self):
        return self

    def __exit__(self, *args):
        return False


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

    def test_reads_every_page(self):
        # 250 reviews: the approval on the head commit is on the third page,
        # and an earlier page has the same reviewer's outdated "changes requested".
        page1 = [review(f"r{i}", state="COMMENTED") for i in range(99)] + [review("carol", state="CHANGES_REQUESTED")]
        page2 = [review(f"s{i}", state="COMMENTED") for i in range(100)]
        page3 = [review(f"t{i}", state="COMMENTED") for i in range(49)] + [review("carol")]
        pages = [FakeResponse(page1, "https://api.github.test/p2"), FakeResponse(page2, "https://api.github.test/p3"),
                 FakeResponse(page3)]
        env = {"PR_NUMBER": "7", "GH_TOKEN": "t", "API_URL": "https://api.github.test",
               "REPOSITORY": "o/r", "PR_AUTHOR": "author"}
        with mock.patch.dict(os.environ, env), \
                mock.patch.object(run.urllib.request, "urlopen", side_effect=pages) as opened:
            self.assertEqual(run.approved_on(HEAD, None), "carol")
        self.assertEqual(opened.call_count, 3)

    def test_unreadable_page_approves_nothing(self):
        pages = [FakeResponse([review("carol")], "https://api.github.test/p2"), OSError("boom")]
        env = {"PR_NUMBER": "7", "GH_TOKEN": "t", "API_URL": "https://api.github.test",
               "REPOSITORY": "o/r", "PR_AUTHOR": "author"}
        with mock.patch.dict(os.environ, env), \
                mock.patch.object(run.urllib.request, "urlopen", side_effect=pages):
            self.assertIsNone(run.approved_on(HEAD, None))

    def test_locked_policy(self):
        self.assertIsNone(self.approved([review("carol", association="OWNER")], approvers=[]))



class FetchTests(unittest.TestCase):
    def test_download_failure_stops_the_action(self):
        import tempfile
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.dict(os.environ, {"IMAGE": "img", "GITHUB_STEP_SUMMARY": f"{tmp}/summary.md"}), \
                mock.patch.object(run.subprocess, "run", return_value=mock.Mock(returncode=3)):
            with self.assertRaises(SystemExit) as stopped:
                run.fetch(Path(tmp), Path(tmp), "base", Path(tmp) / "vendor")
            self.assertEqual(stopped.exception.code, 2)
            self.assertIn("could not be downloaded", Path(f"{tmp}/summary.md").read_text())


if __name__ == "__main__":
    unittest.main()
