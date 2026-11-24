import assert from "node:assert/strict";
import { test } from "node:test";
import { keyAction, shortcuts } from "../src/keys";

const press = (key: string, extra: { ctrl?: boolean; inInput?: boolean } = {}) => ({ key, ctrl: false, inInput: false, ...extra });

test("shortcuts run their commands", () => {
  for (const [key, command] of Object.entries(shortcuts)) {
    assert.deepEqual(keyAction(press(key), false), { run: command });
  }
});

test("shortcuts are not taken while typing or with a modifier", () => {
  assert.equal(keyAction(press("s", { inInput: true }), false), null);
  assert.equal(keyAction(press("s", { ctrl: true }), false), null);
});

test("digits pick a branch option only while one is pending", () => {
  assert.deepEqual(keyAction(press("2"), true), { run: "branch 2" });
  assert.equal(keyAction(press("2"), false), null);
});

test("console and help", () => {
  assert.deepEqual(keyAction(press(":"), false), { focusConsole: true });
  assert.deepEqual(keyAction(press("/"), false), { focusConsole: true });
  assert.deepEqual(keyAction(press("?"), false), { help: true });
});

test("other keys do nothing", () => {
  assert.equal(keyAction(press("x"), true), null);
  assert.equal(keyAction(press("Enter"), true), null);
});
