import assert from "node:assert/strict";
import { describe, test } from "node:test";
import { branchArgument, commandEnabled, initialModel, maxLog, pcBreakpoints, update, type Model } from "../src/model";
import { states, stateWith, statsFixture } from "./fixtures";

describe("update", () => {
  test("a command is logged and makes the page busy until it finishes", () => {
    const started = update(initialModel, { type: "started", command: "step 3" });
    assert.equal(started.busy, true);
    assert.deepEqual(started.log, [{ kind: "command", text: "> step 3" }]);
    assert.equal(update(started, { type: "finished" }).busy, false);
  });

  test("a view's output, then its message, are logged", () => {
    const v = stateWith({ output: "the trace", message: "Stopped." });
    const m = update(initialModel, { type: "view", view: v });
    assert.equal(m.view, v);
    assert.deepEqual(m.log, [
      { kind: "output", text: "the trace" },
      { kind: "message", text: "Stopped." },
    ]);
  });

  test("a view without output or message logs nothing", () => {
    const m = update(initialModel, { type: "view", view: stateWith({ output: null, message: "" }) });
    assert.deepEqual(m.log, []);
  });

  test("failures are logged as errors and keep the state", () => {
    const withView = update(initialModel, { type: "view", view: states["branch"]! });
    const m = update(withView, { type: "failed", error: "lost" });
    assert.equal(m.view, withView.view);
    assert.deepEqual(m.log.at(-1), { kind: "error", text: "lost" });
  });

  test("stats and progress are stored", () => {
    const m = update(initialModel, { type: "stats", stats: statsFixture });
    assert.equal(m.stats, statsFixture);
    assert.deepEqual(update(m, { type: "progress", progress: { running: false } }).progress, { running: false });
  });

  test("the log keeps the newest entries", () => {
    let m: Model = initialModel;
    for (let i = 0; i < maxLog + 10; i++) m = update(m, { type: "failed", error: String(i) });
    assert.equal(m.log.length, maxLog);
    assert.equal(m.log[0]?.text, "10");
    assert.equal(m.log.at(-1)?.text, String(maxLog + 9));
  });

  test("update does not change the model it is given", () => {
    const before = JSON.stringify(initialModel);
    update(initialModel, { type: "started", command: "step" });
    assert.equal(JSON.stringify(initialModel), before);
  });
});

describe("helpers", () => {
  test("breakpoints on a pc, with their index", () => {
    const v = stateWith({ breakpoints: ["op SSTORE", "pc 0x2a", "line Foo.sol:3", "pc 0x0"] });
    assert.deepEqual([...pcBreakpoints(v)], [
      [0x2a, 1],
      [0, 3],
    ]);
  });
  test("the argument of a branch option", () => {
    assert.equal(branchArgument(["false", "true"], 0), "false");
    assert.equal(branchArgument(["false", "true"], 1), "true");
    assert.equal(branchArgument(["0x1", "0x2", "0x3"], 2), "2");
  });
  test("which toolbar commands can run", () => {
    const at = (status: "running" | "branch" | "halted", step: number) => stateWith({ status, step });
    assert.equal(commandEnabled(null, "step"), false);
    assert.equal(commandEnabled(at("running", 0), "step"), true);
    assert.equal(commandEnabled(at("running", 0), "back"), false);
    assert.equal(commandEnabled(at("halted", 5), "continue"), false);
    assert.equal(commandEnabled(at("halted", 5), "restart"), true);
    assert.equal(commandEnabled(at("branch", 3), "next"), false);
    assert.equal(commandEnabled(at("branch", 3), "branch true"), true);
  });
});
