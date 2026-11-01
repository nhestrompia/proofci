import hashlib
from contextlib import closing
import tempfile
from pathlib import Path
import unittest

import baselines
import service_baseline

class ServiceBaselineTests(unittest.TestCase):
    def test_only_active_reviewed_baseline_for_repository_can_be_materialized(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            store = root / 'baseline.db'
            manifest = baselines.encoded({'version': 1, 'candidate': 'candidate.lean', 'contracts': [{
                'id': 'p', 'explanation': 'property', 'owner': 'maintainer', 'formal_statement': 'x + 1',
                'assumptions': [], 'specification_closure': [], 'implementation_bindings': ['target'],
                'policy': 'required', 'evidence': 'evidence'}]})
            draft = root / 'draft'; draft.mkdir()
            baseline_digest = baselines.materialize(baselines.parse_manifest(manifest), draft)
            manifest_digest = hashlib.sha256(manifest).hexdigest()
            with baselines.open_store(store) as db:
                db.execute('INSERT INTO baselines (digest, manifest, manifest_path, baseline_sha256, repository, initial_head, approval_identity, approval_source, report) VALUES (?,?,?,?,?,?,?,?,?)',
                           (manifest_digest, manifest, 'contracts.json', baseline_digest, 'https://github.com/owner/repo.git', 'a' * 40, 'reviewer', 'trusted-local-caller', b'{}'))
                db.execute('INSERT INTO active (id, digest) VALUES (1, ?)', (manifest_digest,))
            info = service_baseline.lookup(store, 'https://github.com/owner/repo.git')
            self.assertEqual(info['baseline_sha256'], baseline_digest)
            with self.assertRaises(ValueError): service_baseline.lookup(store, 'https://github.com/other/repo.git')
            output = root / 'output'; output.mkdir()
            service_baseline.materialize(store, 'https://github.com/owner/repo.git', baseline_digest, output)
            self.assertEqual(hashlib.sha256((output / 'baseline.json').read_bytes()).hexdigest(), baseline_digest)
            with self.assertRaises(ValueError): service_baseline.materialize(store, 'https://github.com/owner/repo.git', 'f' * 64, root / 'other')

    def test_baseline_revision_changes_even_when_digest_returns_to_previous_value(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = Path(tmp) / 'baseline.db'
            with closing(baselines.open_store(store)) as db, db:
                db.execute('INSERT INTO active (id, digest) VALUES (1, ?)', ('a',))
                first = db.execute('SELECT revision FROM active_revision WHERE id=1').fetchone()[0]
                db.execute('UPDATE active SET digest=? WHERE id=1', ('b',))
                db.execute('UPDATE active SET digest=? WHERE id=1', ('a',))
                returned = db.execute('SELECT revision FROM active_revision WHERE id=1').fetchone()[0]
                self.assertGreater(returned, first)
                db.execute('DELETE FROM active WHERE id=1')
                db.execute('INSERT INTO active (id, digest) VALUES (1, ?)', ('a',))
                self.assertGreater(db.execute('SELECT revision FROM active_revision WHERE id=1').fetchone()[0], returned)
