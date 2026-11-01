"""Run a real proof in the disposable QEMU verifier."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import proofci

HERE = Path(__file__).resolve().parent
FIXTURES = HERE.parent / 'experiments/source-binding/fixtures'

@unittest.skipUnless(os.environ.get('PROOFCI_TEST_VM'), 'requires local QEMU verifier image')
class VMVerifierTests(unittest.TestCase):
    def test_real_lean_evidence_in_guest(self):
        with tempfile.TemporaryDirectory(prefix='proofci-vm-test-') as temporary:
            root = Path(temporary); snapshot = root / 'snapshot'; snapshot.mkdir()
            shutil.copy(FIXTURES / 'candidate.lean', snapshot / 'candidate.lean')
            shutil.copytree(FIXTURES / 'verified', snapshot / 'evidence')
            def git(*args): return subprocess.check_output(['git', '-C', str(snapshot), *args], text=True).strip()
            git('init', '-q'); git('config', 'user.name', 'ProofCI'); git('config', 'user.email', 'proofci@example.invalid')
            repository = 'https://example.invalid/fixture.git'; git('remote', 'add', 'origin', repository)
            git('add', '.'); git('commit', '-qm', 'fixture'); head = git('rev-parse', 'HEAD')
            protected = root / 'protected'; protected.mkdir()
            shutil.copy(FIXTURES / 'contract.json', protected / 'contract.json')
            sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
            baseline = protected / 'baseline.json'
            baseline.write_text(json.dumps({'version': 1, 'candidate': 'candidate.lean', 'obligations': [{'id': 'increment', 'policy': 'required', 'contract': 'contract.json', 'contract_sha256': sha(protected / 'contract.json'), 'evidence': 'evidence'}]}))
            envelope = root / 'envelope.json'
            envelope.write_text(json.dumps({'version': 1, 'repository': repository, 'head': head, 'base': head,
                'candidate_sha256': sha(snapshot / 'candidate.lean'), 'baseline_sha256': sha(baseline),
                'dependency': sha(proofci.VALIDATOR / 'core-dependencies.json'), 'toolchain': proofci.TOOLCHAIN_SHA256,
                'trust_policy': proofci.policy_digest(), 'resource_policy': {'timeout_seconds': 900, 'cpu_seconds': 900,
                'memory_bytes': 2147483648, 'file_bytes': 2147483648, 'processes': 256}}))
            report = root / 'report.json'
            result = subprocess.run([sys.executable, str(HERE / 'vm_container.py'), '--envelope', str(envelope),
                '--baseline', str(baseline), '--snapshot', str(snapshot), '--report', str(report), '--validator-only'], timeout=960)
            self.assertEqual(result.returncode, 0, report.read_text())
            self.assertEqual(json.loads(report.read_text())['status'], 'passed')
