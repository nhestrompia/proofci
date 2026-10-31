import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest

import dependencies


class DependencyStagingTests(unittest.TestCase):
    def test_stages_content_addressed_files_and_verifies_nested_paths(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cache = root / "cache"
            cache.mkdir()
            data = b"approved dependency"
            checksum = hashlib.sha256(data).hexdigest()
            (cache / checksum).write_bytes(data)
            manifest = {"version": 1, "dependencies": [{"name": "lib/core.bin",
                "sha256": checksum, "size_bytes": len(data)}]}
            manifest_path = root / "manifest.json"
            manifest_path.write_text(json.dumps(manifest))
            staged = root / "staged"
            self.assertEqual(dependencies.stage(manifest_path, cache, staged), manifest)
            self.assertEqual((staged / "lib/core.bin").read_bytes(), data)
            self.assertEqual(dependencies.verify_staged(staged), manifest)

    def test_rejects_urls_traversal_and_cache_symlinks(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cache = root / "cache"
            cache.mkdir()
            data = b"approved"
            checksum = hashlib.sha256(data).hexdigest()
            outside = root / "outside"
            outside.write_bytes(data)
            (cache / checksum).symlink_to(outside)
            manifest = {"version": 1, "dependencies": [{"name": "core",
                "sha256": checksum, "size_bytes": len(data)}]}
            manifest_path = root / "manifest.json"
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):
                dependencies.stage(manifest_path, cache, root / "staged")
            manifest["dependencies"][0]["url"] = "https://attacker.invalid/tool"
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):
                dependencies.read_manifest(manifest_path)
            manifest["dependencies"][0] = {"name": "../escape", "sha256": checksum,
                                            "size_bytes": len(data)}
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):
                dependencies.read_manifest(manifest_path)

    def test_digest_and_size_are_checked_before_staging(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            cache = root / "cache"
            cache.mkdir()
            (cache / ("0" * 64)).write_bytes(b"wrong")
            manifest_path = root / "manifest.json"
            manifest_path.write_text(json.dumps({"version": 1, "dependencies": [{
                "name": "core", "sha256": "0" * 64, "size_bytes": 4}]}))
            with self.assertRaises(ValueError):
                dependencies.stage(manifest_path, cache, root / "staged")


if __name__ == "__main__":
    unittest.main()
