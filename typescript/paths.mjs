// Where non-relative imports in a repository point.

import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { join, relative } from "node:path";
import ts from "typescript";

const ENTRIES = ["src/index.ts", "index.ts", "src/main.ts", "lib/index.ts", "src/index.tsx"];

// Imports between workspace packages and tsconfig aliases, which would
// otherwise look like third-party code because nothing is installed.
export function workspacePaths(root) {
  const paths = {};
  const walk = (dir, depth) => {
    for (const name of readdirSync(dir)) {
      if (name === "node_modules" || name.startsWith(".")) continue;
      const path = join(dir, name);
      let stat;
      try { stat = statSync(path); } catch { continue; }
      if (stat.isDirectory()) { if (depth < 5) walk(path, depth + 1); continue; }
      if (name !== "package.json") continue;
      let manifest;
      try { manifest = JSON.parse(readFileSync(path, "utf8")); } catch { continue; }
      if (typeof manifest.name !== "string") continue;
      const entry = ENTRIES.map(e => join(dir, e)).find(existsSync);
      if (entry) paths[manifest.name] = [entry];
      paths[`${manifest.name}/*`] = [join(dir, "src/*"), join(dir, "*")];
    }
  };
  walk(root, 0);
  for (const name of readdirSync(root)) {
    if (!/^tsconfig.*\.json$/.test(name)) continue;
    const config = ts.readConfigFile(join(root, name), p => readFileSync(p, "utf8")).config;
    const base = join(root, config?.compilerOptions?.baseUrl ?? ".");
    for (const [alias, targets] of Object.entries(config?.compilerOptions?.paths ?? {})) {
      paths[alias] ??= targets.map(target => join(base, target));
    }
  }
  return paths;
}

// The mapping of a protected checkout, pointed at the candidate's files. Taking
// it from the candidate would let a pull request redirect an import to a file the
// real build never loads.
export function protectedPaths(policyRoot, repository) {
  const mapped = {};
  for (const [alias, targets] of Object.entries(workspacePaths(policyRoot))) {
    mapped[alias] = targets.map(target => join(repository, relative(policyRoot, target)));
  }
  return mapped;
}
