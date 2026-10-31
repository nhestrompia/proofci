import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest

from test_proofci import CLITest

REPLAY = Path(__file__).with_name('replay.py')


class ReplayTest(CLITest):
    def invoke(self, *args):
        return subprocess.run([sys.executable, str(REPLAY), *map(str, args)], capture_output=True, text=True)

    def export_bundle(self):
        status, _ = self.run_cli()
        self.assertEqual(status, 1)
        archive = self.root / 'evidence.tar'
        result = self.invoke('export', '--envelope', self.root / 'envelope.json', '--baseline', self.root / 'baseline.json', '--snapshot', self.snapshot, '--report', self.root / 'report.json', '--output', archive)
        self.assertEqual(result.returncode, 0, result.stderr)
        return archive, result.stdout.strip().removeprefix('sha256:')

    def test_export_replay_without_docker_is_nonpassing_with_report(self):
        archive, digest = self.export_bundle()
        output = self.root / 'replay.json'
        result = self.invoke('replay', '--bundle', archive, '--sha256', digest, '--output', output)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(json.loads(output.read_text())['historical_ci_publication'], 'not_reproduced')

    def test_digest_mismatch_rejected(self):
        archive, _ = self.export_bundle()
        output = self.root / 'replay.json'
        result = self.invoke('replay', '--bundle', archive, '--sha256', '0' * 64, '--output', output)
        self.assertEqual(result.returncode, 2)
        self.assertIn('digest mismatch', json.loads(output.read_text())['reason'])

    def test_traversal_rejected_before_extraction(self):
        archive = self.root / 'hostile.tar'
        with tarfile.open(archive, 'w') as tar:
            info = tarfile.TarInfo('../escape')
            info.size = 1
            tar.addfile(info, io.BytesIO(b'x'))
        output = self.root / 'replay.json'
        result = self.invoke('replay', '--bundle', archive, '--sha256', hashlib.sha256(archive.read_bytes()).hexdigest(), '--output', output)
        self.assertEqual(result.returncode, 2)
        self.assertIn('unsafe archive path', json.loads(output.read_text())['reason'])
        self.assertFalse((self.root.parent / 'escape').exists())


if __name__ == '__main__':
    unittest.main()
