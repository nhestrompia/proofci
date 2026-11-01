"""Exercise the protected baseline adapter and real isolated Lean dispatcher."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import baselines
import service_execute

FIXTURES = Path(__file__).resolve().parent.parent / 'experiments/source-binding/fixtures'

@unittest.skipUnless(os.environ.get('PROOFCI_TEST_VM'), 'requires the pinned QEMU image and Docker')
class ServiceExecuteTests(unittest.TestCase):
    def test_active_baseline_dispatches_real_lean_check(self):
        with tempfile.TemporaryDirectory(prefix='proofci-service-test-') as temporary:
            root = Path(temporary)
            snapshot = root / 'snapshot'; snapshot.mkdir()
            shutil.copy(FIXTURES / 'candidate.lean', snapshot / 'candidate.lean')
            shutil.copytree(FIXTURES / 'verified', snapshot / 'evidence')
            manifest = baselines.encoded({'version': 1, 'candidate': 'candidate.lean', 'contracts': [{
                'id': 'increment', 'explanation': 'Adds one', 'owner': 'maintainer', 'formal_statement': 'x + 1',
                'assumptions': [], 'specification_closure': [], 'implementation_bindings': ['target'],
                'policy': 'required', 'evidence': 'evidence'}]})
            (snapshot / 'contracts.json').write_bytes(manifest)
            def git(*args):
                return subprocess.check_output(['git', '-C', str(snapshot), *args], text=True).strip()
            git('init', '-q'); git('config', 'user.name', 'ProofCI'); git('config', 'user.email', 'proofci@example.invalid')
            repository = 'https://example.invalid/fixture.git'
            git('remote', 'add', 'origin', repository); git('add', '.'); git('commit', '-qm', 'fixture')
            head = git('rev-parse', 'HEAD')
            baseline_dir = root / 'prepared'; baseline_dir.mkdir()
            digest = baselines.materialize(baselines.parse_manifest(manifest), baseline_dir)
            manifest_digest = hashlib.sha256(manifest).hexdigest()
            store = root / 'baseline.db'
            with baselines.open_store(store) as db:
                db.execute('INSERT INTO baselines (digest, manifest, manifest_path, baseline_sha256, repository, initial_head, approval_identity, approval_source, report) VALUES (?,?,?,?,?,?,?,?,?)',
                           (manifest_digest, manifest, 'contracts.json', digest, repository, head, 'reviewer', 'test-fixture', b'{}'))
                db.execute('INSERT INTO active (id, digest) VALUES (1, ?)', (manifest_digest,))
            report = root / 'report.json'
            status = service_execute.execute(store=store, repository=repository, head=head, base=head,
                                             baseline_digest=digest, snapshot=snapshot, report=report)
            result = json.loads(report.read_text())
            self.assertEqual(status, 0, result)
            self.assertEqual(result['status'], 'passed')
            self.assertEqual(result['reviewed_baseline_sha256'], manifest_digest)
            self.assertEqual(result['proposed_guarantee_changes'], [])
            self.assertEqual(result['dispatch']['final_status'], 0)
