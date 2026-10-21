import assert from "node:assert/strict";
import { describe, test } from "node:test";
import { progress, stats, view } from "../src/api";
import { SchemaError } from "../src/schema";
import { helpFixture, progressIdle, progressRunning, raw, states, statsFixture } from "./fixtures";

describe("the server's answers parse", () => {
  test("states", () => {
    assert.equal(states["concrete"]!.mode, "concrete");
    assert.equal(states["branch"]!.status, "branch");
    assert.equal(states["halted"]!.status, "halted");
    assert.ok(states["halted"]!.result !== null);
  });
  test("stats", () => {
    assert.ok(statsFixture.counters.opcodes > 0);
  });
  test("progress, running and idle", () => {
    assert.equal(progressRunning.running, true);
    assert.equal(progressIdle.running, false);
  });
  test("help", () => {
    assert.ok(helpFixture.commands.some((c) => c.startsWith("step")));
  });
});

describe("unexpected answers fail with where they differ", () => {
  test("a wrong type", () => {
    assert.throws(() => view.parse({ ...raw.stateConcrete, status: 3 }), /^SchemaError: status: expected one of running, branch, halted/);
  });
  test("a missing nested field", () => {
    const counters: Record<string, unknown> = { ...raw.stats.counters };
    delete counters["opcodes"];
    assert.throws(() => stats.parse({ ...raw.stats, counters }), /counters\.opcodes: expected a number/);
  });
  test("a wrong element of an array", () => {
    assert.throws(() => view.parse({ ...raw.stateConcrete, stack: [{ hex: "0x1" }, "0x2"] }), /stack\[1\]: expected an object/);
    assert.throws(() => view.parse({ ...raw.stateConcrete, stack: [{ hex: 1 }] }), /stack\[0\]\.expr: expected a string/);
  });
  test("neither kind of progress", () => {
    assert.throws(() => progress.parse({ running: "yes" }), /running/);
  });
  test("errors are SchemaErrors", () => {
    try {
      view.parse(null);
      assert.ok(false, "parsed null");
    } catch (e) {
      assert.ok(e instanceof SchemaError);
    }
  });
  test("fields a newer server adds are kept", () => {
    const v = view.parse({ ...raw.stateConcrete, extra: 1 }) as Record<string, unknown>;
    assert.equal(v["extra"], 1);
  });
});
