// What the action runs to bridge TypeScript functions: for each target, a Lean file with the
// function's typed view, its Core, and a theorem saying they agree (see bridge3.mjs).
//
// usage: node action_bridge.mjs <config.json>
// config: { root, repository, policyRoot, viewFile, out, targets, assumes, effects }
// The last line printed is JSON: { results: { [target]: { file } | { reason } } }.
//
// A target that can't be bridged gets a reason, never an exception: the caller reports it as
// tested, not proved. The reason says which feature has no bridge yet where that is known.
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { generate } from "./bridge3.mjs";
import { protectedPaths, workspacePaths } from "../../typescript/paths.mjs";

const config = JSON.parse(readFileSync(process.argv[2], "utf8"));
const viewSource = readFileSync(config.viewFile, "utf8");
const paths = config.policyRoot ? protectedPaths(config.policyRoot, config.repository) : workspacePaths(config.root);
const options = {
  repository: config.repository, policyRoot: config.policyRoot, requireTypes: true,
  assumes: config.assumes ?? [], effects: config.effects ?? [],
};

// Reasons worth naming. Everything else is reported with the generator's own words.
const KNOWN = [
  [/no encoding for (generic|map|tagged|handle)/, m => `a ${m[1] === "handle" ? "handle" : m[1]} type has no bridge encoding yet`],
  [/recursive/i, () => "recursive types have no bridge yet"],
];
function reasonOf(error) {
  const text = String(error?.message ?? error).split("\n")[0].slice(0, 300);
  for (const [pattern, say] of KNOWN) { const m = text.match(pattern); if (m) return say(m); }
  return `the bridge could not be generated: ${text}`;
}

const results = {};
config.targets.forEach((target, index) => {
  try {
    const { text } = generate(config.root, target, paths, { viewSource, options });
    const file = `B${index}.lean`;
    writeFileSync(join(config.out, file), text);
    results[target] = { file };
  } catch (error) {
    results[target] = { reason: reasonOf(error) };
  }
});
console.log(JSON.stringify({ results }));
