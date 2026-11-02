#!/usr/bin/env python3
"""Create an exercise repository, its pull request commits, and its reviewed baseline.

The baseline is activated through the documented operator path, `portable/baselines.py
activate`, which runs the pinned verifier. The authority is bootstrapped with
`portable/authority.py`. Pull request merge commits are real Git merges whose
parents are the base and the head, as GitHub's test merge commits are.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'portable'))
import baselines  # noqa: E402
import proofci  # noqa: E402

FIXTURES = ROOT / 'experiments/source-binding/fixtures'
MANIFEST = {'version': 1, 'candidate': 'candidate.lean', 'contracts': [{'id': 'increment', 'explanation': 'Adds one',
    'owner': 'maintainer', 'formal_statement': 'x + 1', 'assumptions': [], 'specification_closure': [],
    'implementation_bindings': ['target'], 'policy': 'required', 'evidence': 'evidence'}]}


def git(work, *args):
    env = {'PATH': '/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin', 'GIT_CONFIG_NOSYSTEM': '1', 'HOME': str(work),
           'GIT_AUTHOR_NAME': 'ProofCI exercise', 'GIT_AUTHOR_EMAIL': 'exercise@example.invalid',
           'GIT_COMMITTER_NAME': 'ProofCI exercise', 'GIT_COMMITTER_EMAIL': 'exercise@example.invalid',
           'GIT_AUTHOR_DATE': '2026-11-01T00:00:00Z', 'GIT_COMMITTER_DATE': '2026-11-01T00:00:00Z'}
    return subprocess.check_output(['git', '-C', str(work), *args], text=True, env=env).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--name', required=True)
    parser.add_argument('--store', type=Path, required=True)
    parser.add_argument('--actor', type=int, required=True)
    parser.add_argument('--pulls', type=int, default=0)
    parser.add_argument('--unpushed', type=int, action='append', default=[], help='create this pull merge without pushing it')
    args = parser.parse_args()
    slug = args.name.replace('/', '__')
    work = args.root / 'src' / slug
    bare = args.root / 'git' / f'{slug}.git'
    repository = f'https://github.com/{args.name}.git'
    work.mkdir(parents=True)
    bare.parent.mkdir(parents=True, exist_ok=True)
    subprocess.check_call(['git', 'init', '-q', '--bare', str(bare)])
    git(work, 'init', '-q', '-b', 'main')
    git(work, 'remote', 'add', 'origin', repository)
    shutil.copy(FIXTURES / 'candidate.lean', work / 'candidate.lean')
    shutil.copytree(FIXTURES / 'verified', work / 'evidence')
    manifest = baselines.encoded(MANIFEST)
    (work / 'contracts.json').write_bytes(manifest)
    (work / 'README.md').write_text(f'# {args.name}\n\nProofCI operational exercise repository.\n')
    git(work, 'add', '.')
    git(work, 'commit', '-qm', 'Approved increment contract')
    main_head = git(work, 'rev-parse', 'HEAD')
    pulls = {}
    for number in range(1, args.pulls + 1):
        git(work, 'checkout', '-q', '-b', f'pr-{number}', main_head)
        (work / 'notes').mkdir(exist_ok=True)
        (work / 'notes' / f'pr-{number}.md').write_text(f'Change {number} does not touch the verified implementation.\n')
        git(work, 'add', '.')
        git(work, 'commit', '-qm', f'Pull request {number}')
        head = git(work, 'rev-parse', 'HEAD')
        git(work, 'checkout', '-q', '--detach', main_head)
        git(work, 'merge', '-q', '--no-ff', '-m', f'Merge {head} into {main_head}', head)
        merge = git(work, 'rev-parse', 'HEAD')
        parents = git(work, 'rev-list', '--parents', '-n', '1', merge).split()[1:]
        pulls[number] = {'head': head, 'base': main_head, 'merge': merge, 'parents': parents, 'pushed': number not in args.unpushed}
        git(work, 'checkout', '-q', 'main')
    refspecs = ['refs/heads/main:refs/heads/main']
    for number, pull in pulls.items():
        refspecs.append(f'{pull["head"]}:refs/pull/{number}/head')
        if pull['pushed']:
            refspecs.append(f'{pull["merge"]}:refs/pull/{number}/merge')
    subprocess.check_call(['git', '-C', str(work), 'push', '-q', str(bare), *refspecs])

    sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    envelope = {'version': 1, 'repository': repository, 'head': main_head, 'base': main_head,
        'candidate_sha256': sha(work / 'candidate.lean'), 'baseline_sha256': '0' * 64,
        'dependency': sha(proofci.VALIDATOR / 'core-dependencies.json'), 'toolchain': proofci.TOOLCHAIN_SHA256,
        'trust_policy': proofci.policy_digest(), 'resource_policy': json.loads((ROOT / 'portable/resource_limits.json').read_text())}
    activation = args.root / 'activation' / slug
    activation.mkdir(parents=True)
    (activation / 'envelope.json').write_text(json.dumps(envelope))
    args.store.parent.mkdir(parents=True, exist_ok=True)
    python = [sys.executable]
    subprocess.check_call([*python, str(ROOT / 'portable/baselines.py'), 'activate', '--store', str(args.store), '--snapshot', str(work),
        '--envelope', str(activation / 'envelope.json'), '--report', str(activation / 'report.json'), '--manifest-path', 'contracts.json',
        '--reviewed-sha256', baselines.sha(manifest), '--approver', str(args.actor)], timeout=900)
    subprocess.check_call([*python, str(ROOT / 'portable/authority.py'), 'bootstrap', '--store', str(args.store), '--repository', repository,
        '--ref', 'refs/heads/main', '--head', main_head, '--actor', str(args.actor)], stdout=subprocess.DEVNULL, timeout=60)
    print(json.dumps({'repository': repository, 'main': main_head, 'reviewed_sha256': baselines.sha(manifest),
                      'pulls': pulls, 'bare': str(bare), 'activation_report': str(activation / 'report.json')}))


if __name__ == '__main__':
    main()
