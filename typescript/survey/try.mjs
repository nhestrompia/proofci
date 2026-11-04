// Runs the real translator over functions from a survey result and counts what
// it accepts, by the reason it gave. Usage: node survey/try.mjs <repo> <survey.json>
import { readFileSync } from "node:fs";
import { translate } from "../translate.mjs";

const [root, input] = process.argv.slice(2);
const { results } = JSON.parse(readFileSync(input, "utf8"));
const IMPURE = new Set(["async", "ambient-effect", "package-call", "this-state", "module-state", "date", "generator"]);
const pure = results.filter(r => r.logic && !r.name.includes(".") && !r.features.some(f => IMPURE.has(f)) && r.file.endsWith(".ts") && !r.file.startsWith("/"));
const reasons = {};
let accepted = 0;
const reason = text => text.replace(/^[^:]*:\d+: /, "").replace(/`[^`]*`/g, "`_`").replace(/\d+/g, "N").slice(0, 70);
const byFile = Map.groupBy(pure, r => r.file);
for (const [file, group] of byFile) {
  let result;
  try {
    result = translate({ root, module: "M", targets: group.map(r => `${file}::${r.name}`) });
  } catch (error) {
    const key = `crash: ${error.message.slice(0, 60)}`;
    reasons[key] = (reasons[key] ?? 0) + group.length;
    continue;
  }
  for (const r of group) {
    const failure = result.failures[`${file}::${r.name}`];
    if (!failure) accepted += 1;
    else reasons[reason(failure)] = (reasons[reason(failure)] ?? 0) + 1;
  }
}
const top = Object.entries(reasons).sort((a, b) => b[1] - a[1]).slice(0, 14);
console.log(JSON.stringify({ repo: root.split("/").pop(), pure: pure.length, accepted, top }));
