"""Create a real portable bundle for the storage integration test."""
import json
from pathlib import Path
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / 'portable'))
from test_replay import ReplayTest

case = ReplayTest('test_digest_mismatch_rejected')
case.setUp()
try:
    archive, digest = case.export_bundle()
    shutil.copyfile(archive, sys.argv[1])
    envelope = json.loads((case.root / 'envelope.json').read_bytes())
    report = json.loads((case.root / 'report.json').read_bytes())
    print(json.dumps({'digest': digest, 'envelope': envelope, 'report': report}))
finally:
    case.doCleanups()
