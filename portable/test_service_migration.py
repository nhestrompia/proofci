from contextlib import closing
from concurrent.futures import ThreadPoolExecutor
import json
import os
import shutil
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import baselines
import service_migration as migration
from test_baselines import manifest


class MigrationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / 'repo'
        self.repo.mkdir()
        self.git('init', '-q')
        self.git('config', 'user.email', 'test@example.invalid')
        self.git('config', 'user.name', 'Test')
        self.git('remote', 'add', 'origin', 'repo')
        (self.repo / 'candidate.lean').write_text('def target (x : Nat) : Nat := x + 1\n')
        old = manifest()
        old['contracts'].append({**old['contracts'][0], 'id': 'retired'})
        self.old = baselines.encoded(old)
        (self.repo / 'contracts.json').write_bytes(self.old)
        self.git('add', '.')
        self.git('commit', '-qm', 'old')
        old_head = self.git('rev-parse', 'HEAD')
        self.store = self.root / 'store.db'
        with tempfile.TemporaryDirectory() as temp:
            digest = baselines.materialize(old, Path(temp))
        with closing(baselines.open_store(self.store)) as db, db:
            db.execute('INSERT INTO baselines(digest,manifest,manifest_path,baseline_sha256,repository,initial_head,approval_identity,approval_source,report) VALUES(?,?,?,?,?,?,?,?,?)', (baselines.sha(self.old), self.old, 'contracts.json', digest, 'repo', old_head, '1', 'fixture', b'{}'))
            db.execute('INSERT INTO active VALUES(1,?)', (baselines.sha(self.old),))
        new = manifest()
        new['contracts'][0]['explanation'] = 'New policy'
        self.new = baselines.encoded(new)
        (self.repo / 'contracts.json').write_bytes(self.new)
        self.git('add', '.')
        self.git('commit', '-qm', 'replacement')
        self.head = self.git('rev-parse', 'HEAD')
        self.report = self.root / 'report.json'

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.repo), *args], text=True).strip()

    def prepare(self):
        return migration.prepare(str(self.store), 'repo', str(self.repo), self.head, baselines.sha(self.old), baselines.sha(self.new), 42, 'generation')

    def dispatch(self, **kwargs):
        Path(kwargs['report_path']).write_text(json.dumps({'version': 1, 'status': 'passed', 'results': []}))
        return 0

    def active(self):
        with closing(baselines.open_store(self.store)) as db:
            return baselines.lookup(db)['digest']

    def test_concurrent_schema_upgrades_are_serialized(self):
        def upgrade(_):
            with closing(baselines.open_store(self.store)) as db:
                migration.schema(db)
        with ThreadPoolExecutor(max_workers=4) as pool:
            list(pool.map(upgrade, range(4)))
        with closing(baselines.open_store(self.store)) as db:
            self.assertIn('revision', [row[1] for row in db.execute('PRAGMA table_info(active)')])
            self.assertIn('previous_revision', [row[1] for row in db.execute('PRAGMA table_info(migrations)')])

    def test_verified_migration_records_retirement_and_activates(self):
        identifier = self.prepare()
        self.assertEqual(self.active(), baselines.sha(self.old))
        with patch.object(migration.dispatch, 'run', side_effect=self.dispatch):
            self.assertEqual(migration.verify(str(self.store), 'repo', str(self.repo), identifier, str(self.report)), 0)
        self.assertEqual(self.active(), baselines.sha(self.old))
        result = migration.activate(str(self.store), 'repo', identifier, self.head, 42, 'generation')
        self.assertTrue(result['policy_changed'])
        self.assertEqual([item['id'] for item in result['retired_guarantees']], ['retired'])
        self.assertEqual(self.active(), baselines.sha(self.new))

    def test_failure_and_stale_authorization_leave_baseline_unchanged(self):
        identifier = self.prepare()
        with patch.object(migration.dispatch, 'run', side_effect=lambda **kw: (Path(kw['report_path']).write_text('{"status":"blocked"}'), 1)[1]):
            self.assertEqual(migration.verify(str(self.store), 'repo', str(self.repo), identifier, str(self.report)), 1)
        with self.assertRaises(ValueError):
            migration.activate(str(self.store), 'repo', identifier, self.head, 42, 'generation')
        with patch.object(migration.dispatch, 'run', side_effect=self.dispatch):
            migration.verify(str(self.store), 'repo', str(self.repo), identifier, str(self.report))
        for head, actor, generation in [('0' * 40, 42, 'generation'), (self.head, 43, 'generation'), (self.head, 42, 'changed')]:
            with self.assertRaises(ValueError):
                migration.activate(str(self.store), 'repo', identifier, head, actor, generation)
        self.assertEqual(self.active(), baselines.sha(self.old))

    def test_competing_migration_cannot_overwrite_new_baseline(self):
        first, second = self.prepare(), self.prepare()
        with patch.object(migration.dispatch, 'run', side_effect=self.dispatch):
            for identifier in (first, second):
                migration.verify(str(self.store), 'repo', str(self.repo), identifier, str(self.report))
        migration.activate(str(self.store), 'repo', first, self.head, 42, 'generation')
        with self.assertRaises(ValueError):
            migration.activate(str(self.store), 'repo', second, self.head, 42, 'generation')

    def test_authorized_migration_can_restore_historical_baseline(self):
        first, stale = self.prepare(), self.prepare()
        with patch.object(migration.dispatch, 'run', side_effect=self.dispatch):
            migration.verify(str(self.store), 'repo', str(self.repo), first, str(self.report))
            migration.verify(str(self.store), 'repo', str(self.repo), stale, str(self.report))
        migration.activate(str(self.store), 'repo', first, self.head, 42, 'generation')
        (self.repo / 'contracts.json').write_bytes(self.old)
        self.git('add', '.')
        self.git('commit', '-qm', 'restore')
        head = self.git('rev-parse', 'HEAD')
        restore = migration.prepare(str(self.store), 'repo', str(self.repo), head, baselines.sha(self.new), baselines.sha(self.old), 42, 'generation')
        with patch.object(migration.dispatch, 'run', side_effect=self.dispatch):
            migration.verify(str(self.store), 'repo', str(self.repo), restore, str(self.report))
        migration.activate(str(self.store), 'repo', restore, head, 42, 'generation')
        self.assertEqual(self.active(), baselines.sha(self.old))
        with self.assertRaisesRegex(ValueError, 'active baseline changed'):
            migration.activate(str(self.store), 'repo', stale, self.head, 42, 'generation')

    @unittest.skipUnless(os.environ.get('PROOFCI_TEST_VM'), 'requires isolated verifier')
    def test_real_isolated_verification_before_activation(self):
        fixtures = Path(__file__).resolve().parent.parent / 'experiments/source-binding/fixtures'
        shutil.copy(fixtures / 'candidate.lean', self.repo / 'candidate.lean')
        shutil.copytree(fixtures / 'verified', self.repo / 'evidence')
        self.git('add', '.')
        self.git('commit', '-qm', 'evidence')
        self.head = self.git('rev-parse', 'HEAD')
        identifier = self.prepare()
        self.assertEqual(migration.verify(str(self.store), 'repo', str(self.repo), identifier, str(self.report)), 0, self.report.read_text())
        self.assertEqual(self.active(), baselines.sha(self.old))
        result = migration.activate(str(self.store), 'repo', identifier, self.head, 42, 'generation')
        self.assertEqual(result['status'], 'passed')
        self.assertEqual(self.active(), baselines.sha(self.new))

    def test_changed_replacement_and_wrong_head_are_rejected(self):
        with self.assertRaises(ValueError):
            migration.prepare(str(self.store), 'repo', str(self.repo), '0' * 40, baselines.sha(self.old), baselines.sha(self.new), 42, 'generation')
        identifier = self.prepare()
        (self.repo / 'contracts.json').write_text('{}')
        with self.assertRaises(ValueError):
            migration.verify(str(self.store), 'repo', str(self.repo), identifier, str(self.report))
        self.assertEqual(self.active(), baselines.sha(self.old))

if __name__ == '__main__':
    unittest.main()
