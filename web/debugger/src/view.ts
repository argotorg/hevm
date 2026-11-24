// What each pane shows for a model: pure functions to virtual DOM.
import type { Progress, StatsView, View, Word } from "./api";
import { expr, memoryRows, opcode, shownExpr, solidityLines, unwrap, word, type Piece } from "./highlight";
import { branchArgument, pcBreakpoints, type LogEntry } from "./model";
import { h, type Child, type VNode } from "./vdom";

export type Run = (command: string) => void;
export type Copy = (text: string) => void;

const maxValueLines = 12;

// A value, a long expression cut to its first lines with a button to copy all of it
export function valueBlock(w: Word, copy: Copy): VNode[] {
  if ("hex" in w) return [h("pre", { class: "word" }, ...pieces(word(w)))];
  const lines = unwrap(w.expr).split("\n");
  const shown = h("pre", { class: "word" }, ...pieces(expr(lines.slice(0, maxValueLines).join("\n"))));
  if (lines.length <= maxValueLines) return [shown];
  return [
    shown,
    h(
      "div",
      { class: "more" },
      `… ${lines.length - maxValueLines} more lines `,
      h("button", { type: "button", class: "small", title: "copy the whole expression", onClick: () => copy(w.expr) }, "copy"),
    ),
  ];
}

export function hex(n: number): string {
  return "0x" + n.toString(16);
}

function fixed(n: number, digits: number): string {
  return Number.isInteger(n) ? String(n) : n.toFixed(digits);
}

// Pieces as text and spans, classed by their kind for the CSS to colour
export function pieces(ps: Piece[]): Child[] {
  return ps.map((p) => (p.kind === null ? p.text : h("span", { class: p.kind }, p.text)));
}

const badge = (label: string, cls: string): VNode => h("span", { class: `badge ${cls}` }, label);

export function statusBar(v: View): VNode[] {
  return [
    h("span", { class: "step" }, `Step ${v.step}`),
    badge(v.status, `status-${v.status}`),
    badge(v.mode, "mode"),
    h("span", { class: "where" }, `pc ${hex(v.pc)} `, h("b", {}, v.op)),
    h("span", { class: "meta" }, `depth ${v.depth}`),
    v.gas !== null && h("span", { class: "meta" }, `gas ${v.gas}`),
    h("span", { class: "contract", title: `code of ${v.codeContract}` }, v.contract),
    v.branchMode !== "solver" && badge(`branches: ${v.branchMode}`, "setting"),
    !v.simplified && badge("not simplified", "setting"),
  ].filter((n): n is VNode => n !== false);
}

export function codePane(v: View, run: Run): VNode[] {
  const breaks = pcBreakpoints(v);
  const header = h("div", { class: "file" }, v.codeName ?? "code", h("span", { class: "code-addr" }, ` at ${v.codeContract}`));
  return [header, ...v.code.map((line) => {
    const bp = breaks.get(line.pc);
    const cls = ["code-line", line.current ? "current" : "", bp !== undefined ? "has-break" : ""].filter(Boolean).join(" ");
    return h(
      "div",
      {
        class: cls,
        title: bp !== undefined ? "click to delete the breakpoint" : "click to break here",
        onClick: () => run(bp !== undefined ? `delete ${bp}` : `break pc ${hex(line.pc)}`),
      },
      h("span", { class: "gutter" }, bp !== undefined ? "●" : line.current ? "▶" : ""),
      h("span", { class: "addr" }, hex(line.pc)),
      h("span", { class: "op" }, ...pieces(opcode(line.op, line.arg))),
    );
  })];
}

export function sourcePane(v: View): VNode[] {
  if (v.source === null) {
    return [
      h(
        "div",
        { class: "empty" },
        v.generatedCode
          ? "Compiler-generated code, such as ABI decoding or overflow checks: it has no Solidity source. Use 'next' to step to the next source line."
          : "No source map for this code. Run hevm in the project root, with its build output.",
      ),
    ];
  }
  const highlighted = solidityLines(v.source.lines.map((l) => l.text));
  return [
    h("div", { class: "file" }, `${v.source.file}:${v.source.line}`),
    ...v.source.lines.map((l, i) =>
      h(
        "div",
        { class: l.current ? "src-line current" : "src-line" },
        h("span", { class: "lineno" }, l.line),
        h("span", { class: "text" }, ...pieces(highlighted[i] ?? [])),
      ),
    ),
  ];
}

export function stackPane(v: View, copy: Copy): VNode[] {
  if (v.stack.length === 0) return [h("div", { class: "empty" }, "empty")];
  return v.stack.map((w, i) => h("div", { class: "stack-item" }, h("span", { class: "index" }, i), h("div", {}, ...valueBlock(w, copy))));
}

export function memoryPane(v: View, run: Run): VNode[] {
  return [
    h(
      "div",
      { class: "pane-note" },
      `${v.memorySize} bytes`,
      v.memorySize > 128 && " · first 128 shown ",
      v.memorySize > 128 && h("button", { type: "button", class: "small", onClick: () => run(`memory 0 ${Math.min(v.memorySize, 65536)}`) }, "show all"),
    ),
    v.memorySize > 0 &&
      h(
        "pre",
        { class: "memory" },
        ...("hex" in v.memory ? memoryRows(v.memory.hex).flatMap((row, i) => [i > 0 && "\n", ...pieces(row)]) : pieces(shownExpr(v.memory.expr))),
      ),
  ].filter((n): n is VNode => n !== false);
}

export function branchPane(v: View, run: Run): VNode[] {
  if (v.branch === null) {
    return [
      h("div", { class: "empty" }, v.mode === "symbolic" ? "No branch pending." : "Concrete run: no symbolic branches."),
      ...(v.choices.length > 0 ? [h("div", { class: "pane-note" }, "Taken so far:"), ...v.choices.map((c) => h("div", { class: "choice" }, c))] : []),
    ];
  }
  const { options, condition } = v.branch;
  return [
    h("div", { class: "pane-note" }, "Pick a side: keys t / f, or the option's number"),
    h(
      "div",
      { class: "options" },
      ...options.map((opt, i) => h("button", { type: "button", class: "branch-option", onClick: () => run(`branch ${branchArgument(options, i)}`) }, `${i}: ${opt}`)),
    ),
    condition !== null && h("pre", { class: "condition", title: "the branch condition" }, ...pieces(shownExpr(condition))),
  ].filter((n): n is VNode => n !== false);
}

export function storagePane(v: View, copy: Copy): VNode[] {
  if (v.storage.length === 0) return [h("div", { class: "empty" }, "No storage.")];
  return v.storage.map((st) =>
    h(
      "div",
      { class: st.current ? "store current-store" : "store" },
      h("div", { class: "store-head" }, h("span", { class: "store-addr" }, ..."hex" in st.address ? [st.address.hex] : [st.address.expr]), ` · initial storage ${st.initial}`),
      ...(st.slots.length === 0
        ? [h("div", { class: "empty" }, "nothing written")]
        : st.slots.map((sl) => h("div", { class: "slot" }, h("div", {}, ...valueBlock(sl.slot, copy)), h("div", {}, ...valueBlock(sl.value, copy))))),
    ),
  );
}

export function breakpointList(v: View, run: Run): VNode[] {
  if (v.breakpoints.length === 0) return [h("div", { class: "empty" }, "None. Click a line of code, or add one below.")];
  return v.breakpoints.map((b, i) =>
    h("div", { class: "bp" }, h("span", {}, `${i}: ${b}`), h("button", { type: "button", class: "small", title: "delete", onClick: () => run(`delete ${i}`) }, "✕")),
  );
}

export function warningsPane(v: View): VNode[] {
  return v.warnings.map((w) => h("pre", { class: "warning" }, w));
}

export function statsRows(s: StatsView): [string, string][] {
  const c = s.counters;
  return [
    ["opcodes", `${c.opcodes} (${c.replayedOpcodes} replayed going back)`],
    ["commands", `${c.commands} in ${fixed(c.commandSecs, 3)}s`],
    ["solver queries", `${c.queries} in ${fixed(c.querySecs, 3)}s`],
    ["branches", `${c.branchesOffered} offered · ${c.branchesTaken} taken · ${c.infeasibleOptions} infeasible values hidden`],
    ["static decisions", String(c.staticDecisions)],
    ["breakpoint hits", String(c.breakpointHits)],
    ["snapshots", String(s.snapshotCount)],
  ];
}

export function statsPane(s: StatsView | null): VNode[] {
  if (s === null) return [h("div", { class: "empty" }, "…")];
  return [h("table", {}, ...statsRows(s).map(([k, val]) => h("tr", {}, h("th", {}, k), h("td", {}, val))))];
}

export function progressPane(p: Progress | null, busy: boolean): VNode[] {
  if (p === null || !p.running) return [h("div", { class: "empty" }, busy ? "Working…" : "Idle.")];
  const solving = p.queries.inFlight.filter((q) => q.solving);
  return [
    h("div", { class: busy ? "progress-line busy" : "progress-line" }, busy ? "Working · " : "", `${p.queries.done} solver queries done`),
    ...solving.map((q) => h("div", { class: "solving" }, `solving ${q.kind ?? "a query"} for ${fixed(q.secs, 1)}s${q.pc !== undefined ? ` at pc ${hex(q.pc)}` : ""}`)),
    ...(p.hottest.length > 0 ? [h("div", { class: "pane-note" }, "Most solver time:")] : []),
    ...p.hottest.slice(0, 5).map((s) => h("div", { class: "hot" }, `pc ${hex(s.pc)} · ${fixed(s.solveSecs, 2)}s · ${s.queries} queries`)),
  ];
}

export function tracePane(trace: string | null): VNode[] {
  if (trace === null) return [h("div", { class: "empty" }, "…")];
  if (trace.trim() === "") return [h("div", { class: "empty" }, "No calls yet.")];
  return [h("pre", { class: "trace" }, trace)];
}

export function logPane(log: LogEntry[]): VNode[] {
  return log.map((e) => h("pre", { class: `log-${e.kind}` }, e.text));
}
