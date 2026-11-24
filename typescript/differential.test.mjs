import { test } from "node:test";
import assert from "node:assert/strict";

import { generator } from "./differential.mjs";

const hits = (seeds, make) => seeds.map(s => generator(s)(make));

test("generator biases optional toward the nothing value", () => {
  const type = { kind: "optional", inner: { kind: "number" }, nothing: "undefined" };
  const none = hits([...Array(20).keys()], type).filter(v => v === undefined).length;
  assert.ok(none >= 6, `only ${none}/20 generated values were undefined`);
});

test("generator injects hypothesis literals into matching kinds", () => {
  const seeds = [...Array(40).keys()];
  const numbers = hits(seeds, { kind: "number" });
  assert.ok(numbers.every(Number.isSafeInteger));
  const biased = seeds.map(s => generator(s, { numbers: [20], strings: ["admin"] })({ kind: "number" }));
  assert.ok(biased.includes(20), "the `offset = 20` literal never appeared in 40 seeds");
  const strings = seeds.map(s => generator(s, { strings: ["admin"] })({ kind: "string" }));
  assert.ok(strings.includes("admin"), "the `tag = \"admin\"` literal never appeared in 40 seeds");
});

test("generator emits empty arrays sometimes", () => {
  const type = { kind: "array", item: { kind: "number" } };
  assert.ok(hits([...Array(40).keys()], type).some(v => v.length === 0));
});
