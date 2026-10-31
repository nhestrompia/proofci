"""Tests for the untrusted worker artifact handoff."""
import hashlib
import os
from pathlib import Path
import tempfile
import unittest

from worker_artifacts import collect_artifacts


class WorkerArtifactTests(unittest.TestCase):
    def test_collects_only_the_named_regular_files_with_matching_digests(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'solution.lean').write_bytes(b'example')
            expected = {'solution.lean': hashlib.sha256(b'example').hexdigest()}
            self.assertEqual(collect_artifacts(root, expected, 100), {'solution.lean': b'example'})
            (root / 'unexpected').write_bytes(b'x')
            with self.assertRaises(ValueError):
                collect_artifacts(root, expected, 100)

    def test_rejects_symlinks_and_hardlinks(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            outside = root / 'outside'
            outside.write_bytes(b'example')
            bundle = root / 'bundle'
            bundle.mkdir()
            target = bundle / 'solution.lean'
            expected = {'solution.lean': hashlib.sha256(b'example').hexdigest()}
            target.symlink_to(outside)
            with self.assertRaises(ValueError):
                collect_artifacts(bundle, expected, 100)
            target.unlink()
            os.link(outside, target)
            with self.assertRaises(ValueError):
                collect_artifacts(bundle, expected, 100)

    def test_rejects_invalid_identity_and_limits(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'solution.lean').write_bytes(b'example')
            with self.assertRaises(ValueError):
                collect_artifacts(root, {'solution.lean': '0' * 64}, 100)
            with self.assertRaises(ValueError):
                collect_artifacts(root, {'solution.lean': hashlib.sha256(b'example').hexdigest()}, 3)
            with self.assertRaises(ValueError):
                collect_artifacts(root, {'../solution.lean': '0' * 64}, 100)


if __name__ == '__main__':
    unittest.main()
