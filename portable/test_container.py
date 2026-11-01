import importlib.util
import json
import os
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("launcher", Path(__file__).with_name("container.py"))
launcher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(launcher)


class LauncherTests(unittest.TestCase):
    def test_guard_retries_cleanup_when_docker_is_temporarily_unavailable(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            docker = root / "docker"
            marker = root / "attempt"
            docker.write_text('#!/bin/sh\nif [ "$1" = inspect ]; then if [ ! -e "$MARKER" ]; then touch "$MARKER"; echo unavailable >&2; exit 1; fi; echo "no such object" >&2; exit 1; fi\n')
            docker.chmod(0o755)
            env = dict(os.environ, PATH=str(root) + os.pathsep + os.environ["PATH"], MARKER=str(marker))
            guard = subprocess.Popen([sys.executable, str(Path(__file__).with_name("create_guard.py")),
                                      "proofci-test", json.dumps(["docker", "create"])],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=env)
            self.assertEqual(guard.stdout.readline(), b"created\n")
            guard.stdin.close()
            guard.stdout.close()
            self.assertEqual(guard.wait(timeout=6), 0)
            self.assertTrue(marker.exists())

    def test_guard_removes_container_if_launcher_dies_after_handoff(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            docker = root / "docker"
            marker = root / "removed"
            docker.write_text('#!/bin/sh\nif [ "$1" = rm ]; then touch "$MARKER"; fi\nif [ "$1" = inspect ]; then echo "no such object" >&2; exit 1; fi\n')
            docker.chmod(0o755)
            env = dict(os.environ, PATH=str(root) + os.pathsep + os.environ["PATH"], MARKER=str(marker))
            guard = subprocess.Popen([sys.executable, str(Path(__file__).with_name("create_guard.py")),
                                      "proofci-test", json.dumps(["docker", "create"])],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=env)
            self.assertEqual(guard.stdout.readline(), b"created\n")
            guard.stdin.write(b"S")
            guard.stdin.flush()
            guard.stdin.close()
            guard.stdout.close()
            guard.wait(timeout=5)
            self.assertTrue(marker.exists())

    def test_delayed_create_is_removed_after_launcher_disappears(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            docker = root / "docker"
            marker = root / "removed"
            docker.write_text('#!/bin/sh\nif [ "$1" = create ]; then sleep 0.2; fi\nif [ "$1" = rm ]; then touch "$MARKER"; fi\nif [ "$1" = inspect ]; then echo "no such object" >&2; exit 1; fi\n')
            docker.chmod(0o755)
            env = dict(os.environ, PATH=str(root) + os.pathsep + os.environ["PATH"], MARKER=str(marker))
            guard = subprocess.Popen([sys.executable, str(Path(__file__).with_name("create_guard.py")),
                                      "proofci-test", json.dumps(["docker", "create"])],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=env)
            guard.stdin.close()
            guard.stdout.close()
            guard.wait(timeout=5)
            self.assertTrue(marker.exists())

    def test_default_image_falls_back_to_pinned_configuration_id(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            snapshot = root / "snapshot"
            snapshot.mkdir()
            (root / "baseline").write_text("{}")
            (root / "envelope").write_text(json.dumps({"resource_policy": {
                "timeout_seconds": 10, "cpu_seconds": 10, "memory_bytes": 100000000,
                "file_bytes": 100000000, "processes": 10}}))
            args = ["container.py", "--envelope", str(root / "envelope"), "--baseline", str(root / "baseline"),
                    "--snapshot", str(snapshot), "--report", str(root / "report")]
            missing = subprocess.CalledProcessError(1, "docker inspect")
            with (patch.object(sys, "argv", args), patch.object(launcher.os, "getuid", return_value=1000),
                  patch.object(launcher.subprocess, "check_output", side_effect=[missing, launcher.IMAGE_CONFIG_ID, missing]) as inspect):
                self.assertEqual(launcher.main(), 2)
            self.assertEqual(inspect.call_args_list[1].args[0][-1], launcher.IMAGE_CONFIG_ID)
            self.assertNotIn("image identity", json.loads((root / "report").read_text())["reason"])

    def test_rejects_untrusted_image_before_running_it(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "baseline").write_text("{}")
            (root / "envelope").write_text(json.dumps({"resource_policy": {
                "timeout_seconds": 10, "cpu_seconds": 10, "memory_bytes": 100000000,
                "file_bytes": 100000000, "processes": 10}}))
            args = ["container.py", "--envelope", str(root / "envelope"), "--baseline", str(root / "baseline"),
                    "--snapshot", str(root), "--report", str(root / "report")]
            with (patch.object(sys, "argv", args), patch.object(launcher.os, "getuid", return_value=1000),
                  patch.object(launcher.subprocess, "check_output", return_value="sha256:wrong\n"),
                  patch.object(launcher.subprocess, "run") as run):
                self.assertEqual(launcher.main(), 2)
            self.assertIn("image identity", json.loads((root / "report").read_text())["reason"])
            run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
