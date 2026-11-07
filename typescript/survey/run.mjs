// Usage: node --max-old-space-size=8192 survey/run.mjs <repo-dir> <output.json>
import { writeFileSync } from "node:fs";
import { adoptionOrder, details, analyze, listFiles, programFor, summarize, workspacePaths } from "./analyze.mjs";

const [root, output] = process.argv.slice(2);
const files = listFiles(root);
const results = analyze(programFor(files, workspacePaths(root)));
const summary = { repo: root.split("/").pop(), files: files.length, ...summarize(results), order: adoptionOrder(results) };
writeFileSync(output, `${JSON.stringify({ summary, details, results: results.map(r => ({ ...r, file: r.file.startsWith(root) ? r.file.slice(root.length + 1) : r.file })) })}\n`);
console.log(JSON.stringify(summary));
