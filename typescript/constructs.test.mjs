// Sync test for the ProofCI agent skill (docs/skills/proofci). Every construct the
// skill lists as supported must still translate, and every construct it lists as
// refused must still fail, so the table an adopting agent reads can't drift from
// the translator. Each `source` is compiled as a whole a.ts with a.ts::f the target.
import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { after, test } from "node:test";
import { translate } from "./translate.mjs";

const tablePath = join(dirname(fileURLToPath(import.meta.url)), "..", "docs", "skills", "proofci", "constructs.json");
const table = JSON.parse(readFileSync(tablePath, "utf8"));

const dir = mkdtempSync(join(tmpdir(), "constructs-"));
after(() => rmSync(dir, { recursive: true, force: true }));
let count = 0;

function outcome(source) {
  const root = join(dir, `p${count++}`);
  mkdirSync(root);
  writeFileSync(join(root, "a.ts"), source);
  const result = translate({ root, module: "M", targets: ["a.ts::f"] });
  return result.failures["a.ts::f"] ?? result.fatal;
}

for (const entry of table.supported) {
  test(`skill table: "${entry.construct}" translates`, () => {
    const reason = outcome(entry.source);
    assert.ok(!reason, `refused:\n${reason}\nin\n${entry.source}`);
  });
}

for (const entry of table.refused) {
  test(`skill table: "${entry.construct}" is refused`, () => {
    const reason = outcome(entry.source);
    assert.ok(reason, `accepted:\n${entry.source}`);
  });
}
