import assert from "node:assert/strict";
import { test } from "node:test";
import { findAll, h, hasClass, textOf } from "../src/vdom";

test("children that are false, null or undefined are left out", () => {
  const node = h("div", {}, "a", false, null, undefined, 0, h("span", {}, "b"));
  assert.equal(node.children.length, 3);
  assert.equal(textOf(node), "a0b");
});

test("findAll and hasClass", () => {
  const tree = h("div", { class: "a b" }, h("span", { class: "b" }), h("span", { class: "c" }, h("i", { class: "b" })));
  assert.equal(findAll(tree, (n) => hasClass(n, "b")).length, 3);
  assert.ok(!hasClass(tree, "ab"));
});
