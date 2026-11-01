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

    def test_export_requires_complete_history_for_distinct_base_and_head(self):
        envelope_path = self.root / 'envelope.json'
        envelope = json.loads(envelope_path.read_text())
        initial = envelope['base']
        (self.snapshot / 'base-marker.txt').write_text('base\n')
        subprocess.run(['git', '-C', str(self.snapshot), 'add', 'base-marker.txt'], check=True)
        subprocess.run(['git', '-C', str(self.snapshot), 'commit', '-qm', 'base'], check=True)
        base = subprocess.check_output(['git', '-C', str(self.snapshot), 'rev-parse', 'HEAD'], text=True).strip()
        subprocess.run(['git', '-C', str(self.snapshot), 'checkout', '-qb', 'feature', initial], check=True)
        (self.snapshot / 'marker.txt').write_text('change\n')
        subprocess.run(['git', '-C', str(self.snapshot), 'add', 'marker.txt'], check=True)
        subprocess.run(['git', '-C', str(self.snapshot), 'commit', '-qm', 'change'], check=True)
        subprocess.run(['git', '-C', str(self.snapshot), 'checkout', '-qb', 'test-base', base], check=True)
        subprocess.run(['git', '-C', str(self.snapshot), 'merge', '--quiet', '--no-ff', '-m', 'test merge', 'feature'], check=True)
        head = subprocess.check_output(['git', '-C', str(self.snapshot), 'rev-parse', 'HEAD'], text=True).strip()
        envelope['head'] = head
        envelope['base'] = base
        envelope_path.write_text(json.dumps(envelope))
        archive, _ = self.export_bundle()
        self.assertTrue(archive.is_file())
        with tarfile.open(archive, 'r:') as tar:
            bundled_repo = self.root / 'repository.bundle'
            bundled_repo.write_bytes(tar.extractfile('repository.bundle').read())
        restored = self.root / 'restored'
        subprocess.run(['git', 'clone', '--quiet', '--no-checkout', str(bundled_repo), str(restored)], check=True)
        for commit in (head, base):
            subprocess.run(['git', '-C', str(restored), 'cat-file', '-e', f'{commit}^{{commit}}'], check=True)
        shallow = self.root / 'shallow'
        subprocess.run(['git', 'clone', '--quiet', '--depth=1', self.snapshot.as_uri(), str(shallow)], check=True)
        subprocess.run(['git', '-C', str(shallow), 'fetch', '--quiet', '--depth=1', self.snapshot.as_uri(), base], check=True)
        subprocess.run(['git', '-C', str(shallow), 'remote', 'set-url', 'origin', 'repo'], check=True)
        result = self.invoke('export', '--envelope', envelope_path, '--baseline', self.root / 'baseline.json',
                             '--snapshot', shallow, '--report', self.root / 'report.json', '--output', self.root / 'shallow.tar')
        self.assertEqual(result.returncode, 2)
        self.assertIn('complete history', result.stderr)

    def test_compressed_repository_expansion_is_rejected(self):
        large = self.snapshot / 'large.bin'
        with large.open('wb') as stream:
            stream.truncate(129 * 1024 * 1024)
        subprocess.run(['git', '-C', str(self.snapshot), 'add', 'large.bin'], check=True)
        subprocess.run(['git', '-C', str(self.snapshot), 'commit', '-qm', 'large'], check=True)
        head = subprocess.check_output(['git', '-C', str(self.snapshot), 'rev-parse', 'HEAD'], text=True).strip()
        path = self.root / 'envelope.json'
        envelope = json.loads(path.read_text())
        envelope['head'] = head
        path.write_text(json.dumps(envelope))
        status, _ = self.run_cli()
        self.assertEqual(status, 1)
        result = self.invoke('export', '--envelope', path, '--baseline', self.root / 'baseline.json',
                             '--snapshot', self.snapshot, '--report', self.root / 'report.json',
                             '--output', self.root / 'evidence.tar')
        self.assertEqual(result.returncode, 2)
        self.assertIn('expanded repository exceeds', result.stderr)

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
