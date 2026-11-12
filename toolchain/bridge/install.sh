#!/bin/sh
# Builds the Lean libraries of the TypeScript bridge into /opt/proofci/spike/core (run as root, once per image).
set -e
cd /opt/proofci/spike/core
cp /tmp/bridge-lakefile.lean lakefile.lean
PYTHONPATH=/opt/proofci python3 -c "
import json
from proofci.lean import _lake_manifest
open('lake-manifest.json', 'w').write(json.dumps(_lake_manifest('proofci_bridge'), indent=1))"
export PATH=/opt/lean/bin:$PATH
lake build Spike.Tac
chmod -R a+rX /opt/proofci/spike
