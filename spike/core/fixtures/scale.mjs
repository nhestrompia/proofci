// Writes functions of growing size, to see how bridge cost grows.
import { writeFileSync } from "node:fs";
const out = [];
for (const k of [2, 6, 12, 40, 160]) {          // k independent ifs in a row: 2^k paths if handled badly
  const lines = [`export function joins${k}(a: number): number {`, "  let t = 0;"];
  for (let i = 0; i < k; i += 1) lines.push(`  if (a > ${i}) { t = t + ${i + 1}; }`);
  lines.push("  return t;", "}");
  out.push(lines.join("\n"));
}
for (const n of [10, 40, 160, 640]) {                 // a long straight line: n assignments
  const lines = [`export function line${n}(a: number): number {`, "  let t = a;"];
  for (let i = 0; i < n; i += 1) lines.push(`  t = t + 1;`);
  lines.push("  return t;", "}");
  out.push(lines.join("\n"));
}
for (const n of [5, 20, 80, 320]) {                   // an early-return chain: n paths
  const lines = [`export function chain${n}(a: number): number {`];
  for (let i = 0; i < n; i += 1) lines.push(`  if (a === ${i}) return ${i * 2};`);
  lines.push("  return -1;", "}");
  out.push(lines.join("\n"));
}
writeFileSync(process.argv[2], out.join("\n\n") + "\n");
