"""Copy bounded raw evidence from a stopped worker into trusted memory."""
import hashlib
import json
import os
from pathlib import Path
import re
import stat

LIMITS = {
    'manifest.json': 64 * 1024,
    'solution.lean': 64 * 1024,
    'challenge.ndjson': 8 * 1024 * 1024,
    'solution.ndjson': 8 * 1024 * 1024,
}


def read_identities(path):
    """Read the trusted caller's allowlist for a raw worker handoff."""
    data = Path(path).read_bytes()
    if len(data) > 64 * 1024:
        raise ValueError('artifact manifest exceeds size limit')
    def unique(pairs):
        result = {}
        for key, item in pairs:
            if key in result:
                raise ValueError('duplicate artifact manifest field')
            result[key] = item
        return result
    value = json.loads(data, object_pairs_hook=unique)
    if not isinstance(value, dict) or set(value) != {'version', 'files'} or value['version'] != 1:
        raise ValueError('invalid artifact manifest')
    identities = value['files']
    if not isinstance(identities, dict):
        raise ValueError('invalid artifact identities')
    return identities


def collect_artifacts(directory, identities, max_bytes):
    """Read only named evidence files. Call after the guest has stopped."""
    if not isinstance(identities, dict) or not identities or len(identities) > len(LIMITS):
        raise ValueError('invalid artifact identities')
    if type(max_bytes) is not int or max_bytes <= 0:
        raise ValueError('invalid artifact size limit')
    if any(name not in LIMITS or not isinstance(value, str) or not re.fullmatch(r'[0-9a-f]{64}', value)
           for name, value in identities.items()):
        raise ValueError('invalid artifact identity')
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    try:
        root = os.open(Path(directory), flags)
        try:
            if set(os.listdir(root)) != set(identities):
                raise ValueError('unexpected or missing artifact')
            result = {}
            total = 0
            for name, expected in identities.items():
                fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=root)
                try:
                    info = os.fstat(fd)
                    limit = min(LIMITS[name], max_bytes - total)
                    if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1 or info.st_size > limit:
                        raise ValueError('invalid artifact file')
                    with os.fdopen(fd, 'rb', closefd=False) as source:
                        data = source.read(limit + 1)
                    final = os.fstat(fd)
                    if ((info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_nlink)
                            != (final.st_dev, final.st_ino, final.st_size, final.st_mtime_ns, final.st_nlink)):
                        raise ValueError('artifact changed while being read')
                    if len(data) != info.st_size or hashlib.sha256(data).hexdigest() != expected:
                        raise ValueError('artifact identity mismatch')
                    total += len(data)
                    result[name] = data
                finally:
                    os.close(fd)
            return result
        finally:
            os.close(root)
    except OSError as error:
        raise ValueError('cannot safely read artifact') from error
