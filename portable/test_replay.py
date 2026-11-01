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

    def test_hosted_ingestion_rejects_a_self_consistent_archive_with_a_substituted_baseline(self):
        archive, _ = self.export_bundle()
        with tarfile.open(archive, 'r:') as tar:
            files = {member.name: tar.extractfile(member).read() for member in tar}
        files['baseline/baseline.json'] = b'{}'
        manifest = json.loads(files['manifest.json'])
        manifest['files']['baseline/baseline.json'] = hashlib.sha256(files['baseline/baseline.json']).hexdigest()
        files['manifest.json'] = json.dumps(manifest).encode()
        with tarfile.open(archive, 'w') as tar:
            for name, data in files.items():
                info = tarfile.TarInfo(name); info.size = len(data)
                tar.addfile(info, io.BytesIO(data))
        digest = hashlib.sha256(archive.read_bytes()).hexdigest()
        result = subprocess.run([sys.executable, str(REPLAY.with_name('check_hosted_bundle.py')), str(archive), digest], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('baseline digest mismatch', result.stderr)

    def test_hosted_ingestion_rejects_unbound_search_results(self):
        archive, _ = self.export_bundle()
        with tarfile.open(archive, 'r:') as tar:
            files = {member.name: tar.extractfile(member).read() for member in tar}
        files['search-results.json'] = b'{}'
        manifest = json.loads(files['manifest.json'])
        manifest['files']['search-results.json'] = hashlib.sha256(files['search-results.json']).hexdigest()
        files['manifest.json'] = json.dumps(manifest).encode()
        with tarfile.open(archive, 'w') as tar:
            for name, data in files.items():
                info = tarfile.TarInfo(name); info.size = len(data)
                tar.addfile(info, io.BytesIO(data))
        result = subprocess.run([sys.executable, str(REPLAY.with_name('check_hosted_bundle.py')), str(archive), hashlib.sha256(archive.read_bytes()).hexdigest()], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('search results digest mismatch', result.stderr)


if __name__ == '__main__':
    unittest.main()
