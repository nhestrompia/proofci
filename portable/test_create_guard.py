"""Check cleanup after a launcher disappears during Docker creation."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest


class CreateGuardTests(unittest.TestCase):
    def test_cleanup_after_parent_pipe_closes_during_creation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            docker = root / 'docker'
            docker.write_text('#!/bin/sh\n'
                              'if [ "$1" = create ]; then sleep 0.3; exit 0; fi\n'
                              'if [ "$1" = rm ]; then touch "$GUARD_REMOVED"; exit 0; fi\n'
                              'echo "No such object" >&2; exit 1\n')
            docker.chmod(0o755)
            marker = root / 'removed'
            env = dict(os.environ, PATH=f'{root}:{os.environ["PATH"]}', GUARD_REMOVED=str(marker))
            guard = subprocess.Popen([sys.executable, str(Path(__file__).with_name('create_guard.py')),
                                      'test-vm', json.dumps(['docker', 'create'])],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.DEVNULL, env=env)
            guard.stdin.close()
            deadline = time.monotonic() + 5
            while not marker.exists() and time.monotonic() < deadline:
                time.sleep(0.05)
            self.assertTrue(marker.exists(), 'guard did not remove the container')
            guard.stdout.close()
            self.assertEqual(guard.wait(timeout=5), 0)


    def test_apple_guard_retries_until_container_is_missing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            runtime = root / 'container'
            marker = root / 'removed'
            runtime.write_text('#!/bin/sh\n'
                               'if [ "$1" = create ]; then sleep 0.3; exit 0; fi\n'
                               'if [ "$1" = delete ]; then touch "$GUARD_REMOVED"; exit 0; fi\n'
                               'echo "container not found: test-vm" >&2; exit 1\n')
            runtime.chmod(0o755)
            env = dict(os.environ, GUARD_REMOVED=str(marker))
            guard = subprocess.Popen([sys.executable, str(Path(__file__).with_name('vm_apple_guard.py')),
                                      str(runtime), 'test-vm', json.dumps([str(runtime), 'create'])],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.DEVNULL, env=env)
            guard.stdin.close()
            self.assertEqual(guard.wait(timeout=5), 0)
            guard.stdout.close()
            self.assertTrue(marker.exists())


if __name__ == '__main__':
    unittest.main()
