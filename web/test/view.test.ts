import assert from "node:assert/strict";
import { describe, test } from "node:test";
import { findAll, h, hasClass, textOf, type VNode } from "../src/vdom";
import * as view from "../src/view";
import { progressIdle, progressRunning, states, stateWith, statsFixture } from "./fixtures";

function recorder(): { run: (c: string) => void; ran: string[] } {
  const ran: string[] = [];
  return { run: (c) => ran.push(c), ran };
}

const all = (nodes: VNode[]): VNode => h("div", {}, ...nodes);
const clickable = (nodes: VNode[]): VNode[] => findAll(all(nodes), (n) => n.props.onClick !== undefined);

describe("status bar", () => {
  test("shows the step, status and position", () => {
    const text = textOf(all(view.statusBar(states["branch"]!)));
    assert.match(text, /step \d+/);
    assert.match(text, /branch/);
    assert.match(text, /symbolic/);
    assert.match(text, /pc 0x[0-9a-f]+ JUMPI/);
  });
  test("shows the settings that are not the default", () => {
    assert.ok(!/merging/.test(textOf(all(view.statusBar(states["concrete"]!)))));
    const text = textOf(all(view.statusBar(stateWith({ merging: true, branchMode: "checked", simplified: false }))));
    assert.match(text, /merging/);
    assert.match(text, /branches: checked/);
    assert.match(text, /not simplified/);
  });
});

describe("code", () => {
  test("marks the current instruction", () => {
    const v = states["concrete"]!;
    const current = findAll(all(view.codePane(v, recorder().run)), (n) => hasClass(n, "current"));
    assert.equal(current.length, 1);
    assert.match(textOf(current[0]!), new RegExp(`0x${v.pc.toString(16)}`));
  });
  test("clicking an instruction sets a breakpoint, clicking it again deletes it", () => {
    const r = recorder();
    const v = states["concrete"]!;
    const lines = clickable(view.codePane(v, r.run));
    lines[0]!.props.onClick!();
    assert.deepEqual(r.ran, [`break pc 0x${v.code[0]!.pc.toString(16)}`]);
    const withBreak = stateWith({ breakpoints: ["op STOP", `pc 0x${v.code[0]!.pc.toString(16)}`] });
    clickable(view.codePane(withBreak, r.run))[0]!.props.onClick!();
    assert.equal(r.ran[1], "delete 1");
  });
});

describe("branch", () => {
  test("a pending branch shows its condition and runs the side picked", () => {
    const r = recorder();
    const nodes = view.branchPane(states["branch"]!, r.run);
    assert.match(textOf(all(nodes)), /Eq/);
    for (const option of clickable(nodes)) option.props.onClick!();
    assert.deepEqual(r.ran, ["branch true", "branch false"]);
  });
  test("a concrete run has no branches", () => {
    assert.match(textOf(all(view.branchPane(states["concrete"]!, recorder().run))), /Concrete run/);
  });
  test("the sides taken so far are listed", () => {
    assert.match(textOf(all(view.branchPane(states["halted"]!, recorder().run))), /Taken so far:.*true/);
  });
});

describe("other panes", () => {
  test("source, without a source map", () => {
    assert.match(textOf(all(view.sourcePane(states["concrete"]!))), /No source map/);
  });
  test("source, with one", () => {
    const v = stateWith({ source: { file: "Foo.sol", line: 2, lines: [{ line: 1, text: "a", current: false }, { line: 2, text: "b", current: true }] } });
    const nodes = view.sourcePane(v);
    assert.match(textOf(all(nodes)), /Foo\.sol:2/);
    assert.equal(findAll(all(nodes), (n) => hasClass(n, "current")).length, 1);
  });
  test("stack, empty and not", () => {
    assert.match(textOf(all(view.stackPane(stateWith({ stack: [] })))), /empty/);
    assert.match(textOf(all(view.stackPane(stateWith({ stack: ["0x1", "0x2"] })))), /0.*0x1.*1.*0x2/);
  });
  test("memory offers the rest when it is long", () => {
    const r = recorder();
    assert.equal(clickable(view.memoryPane(stateWith({ memorySize: 64 }), r.run)).length, 0);
    clickable(view.memoryPane(stateWith({ memorySize: 4096 }), r.run))[0]!.props.onClick!();
    assert.deepEqual(r.ran, ["memory 0 4096"]);
  });
  test("breakpoints can be deleted", () => {
    const r = recorder();
    clickable(view.breakpointList(states["breakpoint"]!, r.run))[0]!.props.onClick!();
    assert.deepEqual(r.ran, ["delete 0"]);
    assert.match(textOf(all(view.breakpointList(stateWith({ breakpoints: [] }), r.run))), /None/);
  });
  test("stats", () => {
    const rows = view.statsRows(statsFixture);
    assert.equal(rows[0]![0], "opcodes");
    assert.match(rows[0]![1], new RegExp(`^${statsFixture.counters.opcodes} `));
    assert.match(textOf(all(view.statsPane(null))), /…/);
  });
  test("progress", () => {
    assert.match(textOf(all(view.progressPane(progressRunning, false))), /solver queries done/);
    assert.match(textOf(all(view.progressPane(progressIdle, false))), /Idle/);
    assert.match(textOf(all(view.progressPane(progressIdle, true))), /Working/);
  });
  test("log entries keep their kind", () => {
    const nodes = view.logPane([{ kind: "error", text: "oops" }]);
    assert.ok(hasClass(nodes[0]!, "log-error"));
    assert.equal(textOf(nodes[0]!), "oops");
  });
});
