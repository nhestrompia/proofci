#!/usr/bin/env python3
"""Validate a hosted bundle before it reaches the object store."""
import json
from pathlib import Path
import sys
import tempfile

import proofci
import replay

files = replay.ingest(Path(sys.argv[1]), sys.argv[2])
with tempfile.TemporaryDirectory(prefix='proofci-bundle-check-') as temporary:
    envelope, report, _, _ = replay.reconstruct(files, Path(temporary))
    print(json.dumps({'envelope': envelope, 'report': report}, separators=(',', ':')))
