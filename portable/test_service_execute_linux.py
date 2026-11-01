"""Exercise the protected baseline adapter and real isolated Lean dispatcher."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from contextlib import nullcontext
from unittest.mock import patch

import baselines
import service_execute
import dispatch

FIXTURES = Path(__file__).resolve().parent.parent / 'experiments/source-binding/fixtures'

@unittest.skipUnless(os.environ.get('PROOFCI_TEST_VM') or os.environ.get('PROOFCI_TEST_PACKAGED'), 'requires the pinned verifier image and Docker')
class ServiceExecuteTests(unittest.TestCase):
    def test_active_baseline_dispatches_real_lean_check(self):
        with tempfile.TemporaryDirectory(prefix='proofci-service-test-') as temporary:
            root = Path(temporary)
            snapshot = root / 'snapshot'; snapshot.mkdir()
            shutil.copy(FIXTURES / 'candidate.lean', snapshot / 'candidate.lean')
            missing_evidence = bool(os.environ.get('PROOFCI_TEST_MISSING_EVIDENCE'))
            if not missing_evidence:
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
            policy_changed = bool(os.environ.get('PROOFCI_TEST_POLICY_CHANGE'))
            if policy_changed:
                proposal = json.loads(manifest)
                proposal['contracts'][0]['explanation'] = 'Changed guarantee description'
                (snapshot / 'contracts.json').write_bytes(baselines.encoded(proposal))
                git('add', '.'); git('commit', '-qm', 'changed proposal')
                head = git('rev-parse', 'HEAD')
            report = root / 'report.json'
            archive = root / 'evidence.tar'
            launcher = nullcontext() if os.environ.get('PROOFCI_TEST_VM') else patch.object(service_execute, 'launch_vm', dispatch._run_process)
            with launcher:
                status = service_execute.execute(store=store, repository=repository, head=head, base=head,
                                                 baseline_digest=digest, snapshot=snapshot, report=report, evidence=archive)
            result = json.loads(report.read_text())
            self.assertEqual(status, 1 if policy_changed or missing_evidence else 0, result)
            self.assertEqual(result['status'], 'blocked' if policy_changed or missing_evidence else 'passed')
            self.assertEqual(result['reviewed_baseline_sha256'], manifest_digest)
            self.assertEqual(bool(result['proposed_guarantee_changes']), policy_changed)
            self.assertEqual(result['dispatch']['final_status'], 1 if missing_evidence else 0)
            if missing_evidence:
                self.assertEqual(result['results'][0]['reason'], 'missing_evidence')
            replay_report = root / 'replay.json'
            replay = subprocess.run(['python3', str(Path(__file__).with_name('replay.py')), 'replay',
                '--bundle', str(archive), '--sha256', hashlib.sha256(archive.read_bytes()).hexdigest(), '--output', str(replay_report)], timeout=240)
            self.assertEqual(replay.returncode, 1 if policy_changed or missing_evidence else 0, replay_report.read_text())
            self.assertEqual(json.loads(replay_report.read_text())['status'], 'reproduced')
            if os.environ.get('PROOFCI_TEST_HOSTED_BUNDLE'):
                shutil.copyfile(archive, os.environ['PROOFCI_TEST_HOSTED_BUNDLE'])
