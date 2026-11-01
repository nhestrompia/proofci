#!/usr/bin/env python3
"""Advance a protected managed branch through the repository authority."""
import argparse
import base64
from contextlib import contextmanager
import json
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

import authority


def environment():
    token = os.environ.get('PROOFCI_GATEWAY_TOKEN')
    if not token:
        raise ValueError('gateway credential unavailable')
    auth = base64.b64encode(('x-access-token:' + token).encode()).decode()
    return {'PATH': '/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin', 'HOME': '/tmp',
            'GIT_CONFIG_GLOBAL': '/dev/null', 'GIT_CONFIG_SYSTEM': '/dev/null',
            'GIT_CONFIG_NOSYSTEM': '1', 'GIT_TERMINAL_PROMPT': '0',
            'GIT_CONFIG_COUNT': '1', 'GIT_CONFIG_KEY_0': 'http.https://github.com/.extraheader',
            'GIT_CONFIG_VALUE_0': 'AUTHORIZATION: basic ' + auth}


@contextmanager
def client(repository, git_dir, ref):
    if not re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+\.git', repository):
        raise ValueError('invalid repository')
    git_dir = Path(git_dir)
    stat = git_dir.lstat()
    if not git_dir.is_absolute() or git_dir.is_symlink() or not git_dir.is_dir() or stat.st_uid != os.getuid() or stat.st_mode & 0o022:
        raise ValueError('git object store must be protected')
    objects = git_dir / 'objects'
    objects_stat = objects.lstat()
    if objects.is_symlink() or not objects.is_dir() or objects_stat.st_uid != os.getuid() or objects_stat.st_mode & 0o022:
        raise ValueError('git objects must be protected')
    env = environment()
    # Never read the supplied repository's config: it can contain includes, URL
    # rewrites, or commands that would receive the gateway credential.
    with tempfile.TemporaryDirectory(prefix='proofci-gateway-') as temporary:
        yield from _client(repository, objects, ref, env, temporary)


def _client(repository, objects, ref, env, temporary):
    clean_git = Path(temporary) / 'git'
    template = Path(temporary) / 'template'
    template.mkdir()
    subprocess.run(['git', 'init', '--bare', '--template=' + str(template), str(clean_git)],
                   env={'PATH': env['PATH'], 'HOME': temporary, 'GIT_CONFIG_NOSYSTEM': '1',
                        'GIT_CONFIG_GLOBAL': '/dev/null'}, stdin=subprocess.DEVNULL,
                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120, check=True)
    env['GIT_OBJECT_DIRECTORY'] = str(objects)
    git = ['git', '-c', 'core.hooksPath=/dev/null', '-c', 'core.fsmonitor=false',
           '-c', 'credential.helper=', '-c', 'protocol.file.allow=never',
           '-c', 'protocol.ext.allow=never', '--git-dir', str(clean_git)]
    def run(args):
        return subprocess.run(git + args, env=env, stdin=subprocess.DEVNULL,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120, check=True)
    run(['check-ref-format', ref])
    if not ref.startswith('refs/heads/'):
        raise ValueError('invalid managed ref')
    yield run


def advance(*, store, repository, git_dir, ref, expected, head):
    if not re.fullmatch(r'[a-f0-9]{40}', expected) or not re.fullmatch(r'[a-f0-9]{40}', head):
        raise ValueError('invalid commit')
    with client(repository, git_dir, ref) as run:
        run(['cat-file', '-e', expected + '^{commit}'])
        run(['cat-file', '-e', head + '^{commit}'])
        run(['merge-base', '--is-ancestor', expected, head])
        change = authority.mutate(store, 'begin', repository, expected=expected, head=head, ref=ref)['change']
        # A crash or uncertain push leaves the authority pending until reconciliation.
        run(['push', '--porcelain', '--force-with-lease=' + ref + ':' + expected, repository, head + ':' + ref])
        observed = run(['ls-remote', '--refs', repository, ref]).stdout.decode().splitlines()
        if observed != [head + '\t' + ref]:
            raise ValueError('remote head does not match pending update')
        authority.mutate(store, 'finish', repository, change=change, head=head)
        return {'change': change, 'head': head}


def recover(*, store, repository, git_dir):
    change = authority.pending(store, repository)
    with client(repository, git_dir, change['ref']) as run:
        observed = run(['ls-remote', '--refs', repository, change['ref']]).stdout.decode().splitlines()
        if observed == [change['new_head'] + '\t' + change['ref']]:
            authority.mutate(store, 'finish', repository, change=change['change'], head=change['new_head'])
            return {'status': 'applied', 'change': change['change']}
        if observed == [change['old_head'] + '\t' + change['ref']]:
            raise ValueError('push outcome remains uncertain; authority stays pending')
        authority.mutate(store, 'quarantine', repository)
        raise ValueError('remote head differs from both sides of the pending change')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=('advance', 'recover'))
    for name in ('store', 'repository', 'git-dir'):
        parser.add_argument('--' + name, required=True)
    for name in ('ref', 'expected', 'head'):
        parser.add_argument('--' + name)
    args = parser.parse_args()
    try:
        if args.operation == 'advance':
            result = advance(store=args.store, repository=args.repository, git_dir=args.git_dir,
                             ref=args.ref, expected=args.expected, head=args.head)
        else:
            result = recover(store=args.store, repository=args.repository, git_dir=args.git_dir)
        print(json.dumps(result))
        return 0
    except (ValueError, TypeError, OSError, subprocess.SubprocessError) as error:
        # Git's stderr and credentials are not safe to return to callers.
        print('managed branch update failed: ' + type(error).__name__, file=sys.stderr)
        return 2

if __name__ == '__main__':
    raise SystemExit(main())
