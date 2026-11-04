// Usage: node --max-old-space-size=8192 survey/run.mjs <repo-dir> <output.json>
import { writeFileSync } from "node:fs";
import { analyze, listFiles, programFor, summarize } from "./analyze.mjs";

const [root, output] = process.argv.slice(2);
const files = listFiles(root);
const results = analyze(programFor(files));
const summary = { repo: root.split("/").pop(), files: files.length, ...summarize(results) };
writeFileSync(output, `${JSON.stringify({ summary, results: results.map(r => ({ ...r, file: r.file.slice(root.length + 1) })) })}\n`);
console.log(JSON.stringify(summary));
