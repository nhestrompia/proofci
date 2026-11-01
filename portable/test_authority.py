from concurrent.futures import ThreadPoolExecutor
from contextlib import closing
from pathlib import Path
import tempfile
import threading
import subprocess
from unittest.mock import patch
import unittest

import authority
import authority_gateway
import baselines
from test_baselines import manifest


class AuthorityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.store = Path(self.temp.name) / 'baseline.db'
        data = baselines.encoded(manifest())
        with closing(baselines.open_store(self.store)) as db, db:
            db.execute('INSERT INTO baselines(digest,manifest,manifest_path,baseline_sha256,repository,initial_head,approval_identity,approval_source,report) VALUES(?,?,?,?,?,?,?,?,?)',
                       (baselines.sha(data), data, 'contracts.json', 'b'*64, 'repo', 'a'*40, '1', 'fixture', b'{}'))
            db.execute('INSERT INTO active VALUES(1,?)', (baselines.sha(data),))
        authority.mutate(self.store, 'bootstrap', 'repo', head='a'*40, actor=1, ref='refs/heads/main')

    def check(self, **kwargs):
        with closing(baselines.open_store(self.store)) as db:
            return authority.checked(db, 'repo', **kwargs)

    def test_head_changes_block_during_pending_and_invalidate_aba(self):
        revision = self.check(head='a'*40, actor=1)
        change = authority.mutate(self.store, 'begin', 'repo', expected='a'*40, head='b'*40, ref='refs/heads/main')['change']
        with self.assertRaisesRegex(ValueError, 'unavailable'):
            self.check(head='a'*40, actor=1)
        authority.mutate(self.store, 'finish', 'repo', change=change, head='b'*40)
        change = authority.mutate(self.store, 'begin', 'repo', expected='b'*40, head='a'*40, ref='refs/heads/main')['change']
        authority.mutate(self.store, 'finish', 'repo', change=change, head='a'*40)
        with self.assertRaisesRegex(ValueError, 'revision changed'):
            self.check(head='a'*40, actor=1, epoch=revision)

    def test_quarantine_fences_pending_change(self):
        pending = authority.mutate(self.store, 'begin', 'repo', expected='a'*40, head='b'*40, ref='refs/heads/main')['change']
        authority.mutate(self.store, 'quarantine', 'repo')
        with self.assertRaises(ValueError):
            authority.mutate(self.store, 'finish', 'repo', change=pending, head='b'*40)
        with self.assertRaises(ValueError):
            self.check()

    def test_revocation_during_pending_is_durable(self):
        change = authority.mutate(self.store, 'begin', 'repo', expected='a'*40, head='b'*40, ref='refs/heads/main')['change']
        authority.mutate(self.store, 'revoke', 'repo', actor=1)
        authority.mutate(self.store, 'finish', 'repo', change=change, head='b'*40)
        with self.assertRaisesRegex(ValueError, 'revoked'):
            self.check(head='b'*40, actor=1)

    def test_finish_is_idempotent(self):
        change = authority.mutate(self.store, 'begin', 'repo', expected='a'*40, head='b'*40, ref='refs/heads/main')['change']
        authority.mutate(self.store, 'finish', 'repo', change=change, head='b'*40)
        self.assertTrue(authority.mutate(self.store, 'finish', 'repo', change=change, head='b'*40)['already_applied'])

    def test_gateway_finishes_only_after_remote_confirms_target(self):
        repository = 'https://github.com/example/fixture.git'
        with closing(baselines.open_store(self.store)) as db, db:
            db.execute('UPDATE baselines SET repository=?', (repository,))
            db.execute('UPDATE authority_state SET repository=?', (repository,))
        git_dir = Path(self.temp.name) / 'objects.git'
        git_dir.mkdir(mode=0o700)
        (git_dir / 'objects').mkdir(mode=0o700)
        calls = []
        def git(args, **_kwargs):
            calls.append(args)
            output = ('b'*40 + '\trefs/heads/main\n').encode() if 'ls-remote' in args else b''
            return subprocess.CompletedProcess(args, 0, output, b'')
        with patch.dict('os.environ', {'PROOFCI_GATEWAY_TOKEN': 'fixture'}), patch.object(authority_gateway.subprocess, 'run', side_effect=git):
            result = authority_gateway.advance(store=self.store, repository=repository, git_dir=str(git_dir),
                ref='refs/heads/main', expected='a'*40, head='b'*40)
        self.assertEqual(result['head'], 'b'*40)
        with closing(baselines.open_store(self.store)) as db:
            authority.checked(db, repository, head='b'*40, ref='refs/heads/main')
        self.assertTrue(any('push' in call for call in calls))

    def test_uncertain_gateway_push_keeps_authority_pending(self):
        repository = 'https://github.com/example/fixture.git'
        with closing(baselines.open_store(self.store)) as db, db:
            db.execute('UPDATE baselines SET repository=?', (repository,))
            db.execute('UPDATE authority_state SET repository=?', (repository,))
        git_dir = Path(self.temp.name) / 'objects.git'
        git_dir.mkdir(mode=0o700)
        (git_dir / 'objects').mkdir(mode=0o700)
        def git(args, **_kwargs):
            if 'push' in args:
                raise subprocess.CalledProcessError(1, args)
            return subprocess.CompletedProcess(args, 0, b'', b'')
        with patch.dict('os.environ', {'PROOFCI_GATEWAY_TOKEN': 'fixture'}), patch.object(authority_gateway.subprocess, 'run', side_effect=git):
            with self.assertRaises(subprocess.CalledProcessError):
                authority_gateway.advance(store=self.store, repository=repository, git_dir=str(git_dir),
                    ref='refs/heads/main', expected='a'*40, head='b'*40)
        with closing(baselines.open_store(self.store)) as db:
            with self.assertRaisesRegex(ValueError, 'unavailable'):
                authority.checked(db, repository)

    def test_gateway_reconciles_interrupted_push_and_quarantines_divergence(self):
        repository = 'https://github.com/example/fixture.git'
        with closing(baselines.open_store(self.store)) as db, db:
            db.execute('UPDATE baselines SET repository=?', (repository,))
            db.execute('UPDATE authority_state SET repository=?', (repository,))
        git_dir = Path(self.temp.name) / 'objects.git'
        git_dir.mkdir(mode=0o700)
        (git_dir / 'objects').mkdir(mode=0o700)
        def recover_at(head):
            def git(args, **_kwargs):
                output = (head + '\trefs/heads/main\n').encode() if 'ls-remote' in args else b''
                return subprocess.CompletedProcess(args, 0, output, b'')
            with patch.dict('os.environ', {'PROOFCI_GATEWAY_TOKEN': 'fixture'}), patch.object(authority_gateway.subprocess, 'run', side_effect=git):
                return authority_gateway.recover(store=self.store, repository=repository, git_dir=str(git_dir))
        authority.mutate(self.store, 'begin', repository, expected='a'*40, head='b'*40, ref='refs/heads/main')
        self.assertEqual(recover_at('b'*40)['status'], 'applied')
        authority.mutate(self.store, 'begin', repository, expected='b'*40, head='c'*40, ref='refs/heads/main')
        with self.assertRaisesRegex(ValueError, 'uncertain'):
            recover_at('b'*40)
        with closing(baselines.open_store(self.store)) as db:
            with self.assertRaisesRegex(ValueError, 'unavailable'):
                authority.checked(db, repository)
        with self.assertRaisesRegex(ValueError, 'differs'):
            recover_at('d'*40)
        with closing(baselines.open_store(self.store)) as db:
            with self.assertRaisesRegex(ValueError, 'unavailable'):
                authority.checked(db, repository)

    def test_recovery_cannot_release_a_delayed_push(self):
        repository = 'https://github.com/example/fixture.git'
        with closing(baselines.open_store(self.store)) as db, db:
            db.execute('UPDATE baselines SET repository=?', (repository,))
            db.execute('UPDATE authority_state SET repository=?', (repository,))
        git_dir = Path(self.temp.name) / 'objects.git'
        git_dir.mkdir(mode=0o700)
        (git_dir / 'objects').mkdir(mode=0o700)
        push_started = threading.Event()
        release_push = threading.Event()
        remote = ['a'*40]
        def git(args, **_kwargs):
            if 'push' in args:
                push_started.set()
                if not release_push.wait(5):
                    raise RuntimeError('test push timed out')
                remote[0] = 'b'*40
            output = (remote[0] + '\trefs/heads/main\n').encode() if 'ls-remote' in args else b''
            return subprocess.CompletedProcess(args, 0, output, b'')
        with patch.dict('os.environ', {'PROOFCI_GATEWAY_TOKEN': 'fixture'}), patch.object(authority_gateway.subprocess, 'run', side_effect=git):
            with ThreadPoolExecutor(max_workers=1) as pool:
                task = pool.submit(authority_gateway.advance, store=self.store, repository=repository,
                    git_dir=str(git_dir), ref='refs/heads/main', expected='a'*40, head='b'*40)
                try:
                    self.assertTrue(push_started.wait(5))
                    with self.assertRaisesRegex(ValueError, 'uncertain'):
                        authority_gateway.recover(store=self.store, repository=repository, git_dir=str(git_dir))
                    with closing(baselines.open_store(self.store)) as db:
                        with self.assertRaisesRegex(ValueError, 'unavailable'):
                            authority.checked(db, repository)
                finally:
                    release_push.set()
                self.assertEqual(task.result()['head'], 'b'*40)

    def test_competing_head_updates_have_one_winner(self):
        def begin(head):
            try:
                authority.mutate(self.store, 'begin', 'repo', expected='a'*40, head=head, ref='refs/heads/main')
                return True
            except ValueError:
                return False
        with ThreadPoolExecutor(max_workers=2) as pool:
            self.assertEqual(sorted(pool.map(begin, ['b'*40, 'c'*40])), [False, True])

if __name__ == '__main__':
    unittest.main()
