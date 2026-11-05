// Writes a Node comparison for each bridged function, using the action's own differential
// check. Together with a bridge, this ties Node to Core: Node matches the typed view on
// these inputs, and the view matches Core by proof.
import { readFileSync, writeFileSync, mkdirSync, existsSync } from "node:fs";
import { join } from "node:path";
import { translate } from "../../typescript/translate.mjs";
import { workspacePaths } from "../../typescript/survey/analyze.mjs";
const [listDir, outDir, corpus] = process.argv.slice(2);
const index = JSON.parse(readFileSync(join(listDir, "index.json"), "utf8"));
for (const x of index) {
  if (!x.ok) continue;
  const res = join(listDir, `F${x.i}.res`), lean = join(listDir, `F${x.i}.out`);
  if (!existsSync(res) || readFileSync(res, "utf8").split(" ")[0] !== "0" || readFileSync(lean, "utf8").includes("sorryAx")) continue;
  const root = `${corpus}/${x.repo}`, target = `${x.file}::${x.fn}`, dir = join(outDir, `F${x.i}`);
  const module = `V${x.i}`;
  const view = translate({ root, module, paths: workspacePaths(root), targets: [target] });
  mkdirSync(dir, { recursive: true });
  writeFileSync(join(dir, `${module}.lean`), view.source);
  writeFileSync(join(dir, "config.json"), JSON.stringify({ root, out: dir, module, cases: 40, signatures: view.signatures, files: view.files, imports: view.imports }));
}
