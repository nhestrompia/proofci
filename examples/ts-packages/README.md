# A project with packages

`src/longitude.ts` takes its `Position` type from `@types/geojson`, so the type checker
needs that package. ProofCI installs it from `package-lock.json` before the check:
with `--ignore-scripts`, with the project's package manager settings left out, and only
from the public npm registry.

Locally, install the packages once and hand them to `dev` and `check`:

```sh
docker run --rm $OPTS -v "$PWD:/base:ro" -v "$PWD:/head:ro" -v "$PWD/.proofci-vendor:/vendor" \
  $IMAGE fetch --base /base --head /head --out /vendor
docker run --rm --network none $OPTS -v "$PWD:/repo:ro" -v "$PWD/.proofci-vendor:/vendor:ro" \
  -v proofci-dev:/tmp/proofci-dev $IMAGE dev --repo /repo --vendor /vendor
```

Without them, the check says which packages are missing instead of proving anything.

The theorem is about every list that starts with a longitude. An empty `Position`
makes the JavaScript return `undefined`, so nothing is claimed there.
