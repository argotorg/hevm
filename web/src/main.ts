import "./style.css";
import { buildArgs, parseOutcome, progressPath, stripAnsi, type Mode, type Outcome, type Request } from "./hevm";
import { compile, onHevmOutput, runHevm } from "./client";
import { $, button, el } from "./dom";
import { setupEquivalence } from "./eqTab";
import { examples } from "./examples";
import { SolidityEditor } from "./editor";
import { segments, tokens } from "./highlight";
import { newStats, onProgress, onStdout, testsDone, type Stats } from "./progress";
import { describeResult, parseTestOutput, type TestResult } from "./results";
import { solExamples } from "./solExamples";
import type { CompileError, Project } from "./solc";
import type { DebugSession } from "./debugger-page";
import type { WorkerStream } from "./worker";

const log = $<HTMLElement>("log");
onHevmOutput((text) => (log.textContent = text));
const sourcePath = "src/Main.sol";

// --- tabs ---

function showTab(name: string) {
  document.body.dataset.tab = name;
}

for (const tab of document.querySelectorAll<HTMLButtonElement>(".tabs button")) {
  tab.addEventListener("click", () => showTab(tab.dataset.tab!));
}

// --- the debugger tab, a page of its own in an iframe ---

const debugFrame = $<HTMLIFrameElement>("debugger");
const debugHint = $<HTMLElement>("debug-hint");
let debugSession: DebugSession | undefined;

window.addEventListener("message", (e) => {
  if (e.source === debugFrame.contentWindow && e.data?.kind === "hevm-debugger-ready" && debugSession) {
    debugFrame.contentWindow!.postMessage(debugSession, "*");
  }
});

function openDebugger(args: string[]) {
  if (!lastProject) return;
  debugSession = { kind: "hevm-debug", files: lastProject.files, args };
  debugHint.hidden = true;
  debugFrame.hidden = false;
  // a fresh page for each session
  debugFrame.src = `debugger/index.html?session=${Date.now()}`;
  showTab("debug");
}

/** The runtime code of a compiled contract, e.g. "src/Main.sol:Example" */
function runtimeCode(contract: string): string | undefined {
  const [path, name] = contract.split(":");
  const artifact = lastProject?.files[`out/${path!.split("/").pop()}/${name}.json`];
  return artifact ? (JSON.parse(artifact) as { deployedBytecode: { object: string } }).deployedBytecode.object : undefined;
}

function openInBytecode(t: TestResult, calldata?: string) {
  const code = runtimeCode(t.contract);
  if (!code) return;
  load(calldata ? { mode: "exec", code, calldata } : { mode: "symbolic", code, sig: t.name });
  outcome.replaceChildren();
  showTab("bytecode");
}

// --- Solidity ---

const solForm = $<HTMLFormElement>("sol-form");
const solExample = $<HTMLSelectElement>("sol-example");
const prove = $<HTMLButtonElement>("prove");
const solStatus = $<HTMLElement>("sol-status");
const solResults = $<HTMLElement>("sol-results");
const solProgress = $<HTMLElement>("sol-progress");

/** A few highlighted lines of the source around a line, marked from the column on */
function excerpt(text: string, line: number, column: number, length: number) {
  const lines = text.split("\n");
  const starts: number[] = [];
  lines.reduce((off, l) => (starts.push(off), off + l.length + 1), 0);
  const toks = tokens(text);
  const markFrom = (starts[line - 1] ?? 0) + column - 1;
  const pre = el("pre", "excerpt");
  for (let n = Math.max(1, line - 2); n <= Math.min(lines.length, line + 2); n++) {
    const row = el("div", n === line ? "hit" : undefined);
    row.append(el("span", "ln", String(n)));
    const from = starts[n - 1]!;
    let mark: HTMLElement | undefined;
    for (const seg of segments(text, toks, from, from + lines[n - 1]!.length,
                               n === line ? [markFrom, markFrom + length] : undefined)) {
      const piece = seg.cls ? el("span", seg.cls, seg.text) : document.createTextNode(seg.text);
      if (!seg.marked) {
        mark = undefined;
        row.append(piece);
      } else {
        if (!mark) row.append((mark = el("mark")));
        mark.append(piece);
      }
    }
    pre.append(row);
  }
  pre.addEventListener("click", () => editor.selectLine(line));
  pre.title = "Show in the editor";
  return pre;
}

function lineCol(text: string, offset: number) {
  const before = text.slice(0, offset);
  const line = before.split("\n").length;
  return { line, column: offset - before.lastIndexOf("\n") };
}

function renderErrors(errors: CompileError[]) {
  for (const e of errors) {
    const card = el("article", `card ${e.severity === "error" ? "fail" : "note"}`);
    card.append(el("h3", undefined, `${e.severity === "error" ? "Error" : "Warning"}: ${e.message}`));
    if (e.file === sourcePath && e.start !== undefined && e.end !== undefined) {
      const { line, column } = lineCol(editor.value, e.start);
      failingLines.push(line);
      card.append(excerpt(editor.value, line, column, Math.max(1, e.end - e.start)));
    }
    solResults.append(card);
  }
}

function renderTest(t: TestResult) {
  const card = el("article", `card ${t.status}`);
  const head = el("h3");
  head.append(el("span", `badge ${t.status}`, t.status.toUpperCase()), ` ${t.name}`);
  card.append(head);
  if (t.status === "running" && !t.counterexamples.length) card.append(el("p", "muted", "Checking…"));
  if (t.status === "pass" && !t.counterexamples.length) {
    card.append(el("p", "muted", "No input breaks it."));
  }
  const debugArgs = ["test", "--root", "/", "--match", `^${t.name.split("(")[0]}$`, "--interactive"];
  for (const c of t.counterexamples) {
    const dl = el("dl");
    dl.append(el("dt", undefined, "Counterexample"), el("dd", "mono", c.calldata));
    dl.append(el("dt", undefined, "Result"), el("dd", undefined, describeResult(c.result)));
    if (c.validated === false) dl.append(el("dt"), el("dd", "muted", "could not be reproduced concretely"));
    card.append(dl);
    if (c.at && c.at.file === sourcePath) {
      failingLines.push(c.at.line);
      card.append(el("p", "where", `Fails at line ${c.at.line}:`));
      card.append(excerpt(editor.value, c.at.line, c.at.column, c.at.code.length));
    } else if (c.at) {
      card.append(el("p", "where", `Fails at ${c.at.file}:${c.at.line}: ${c.at.code}`));
    }
    const raw = c.raw;
    if (raw) {
      const actions = el("div", "card-actions");
      actions.append(
        button("Replay in debugger", () => openDebugger([...debugArgs, "--calldata", raw])),
        button("Open in Bytecode tab", () => openInBytecode(t, raw)),
      );
      card.append(actions);
    }
  }
  for (const n of t.notes) card.append(el("p", "muted", n));
  if (t.status !== "running") {
    const actions = el("div", "card-actions");
    actions.append(button("Debug symbolically", () => openDebugger(debugArgs)));
    if (!t.counterexamples.length) actions.append(button("Open in Bytecode tab", () => openInBytecode(t)));
    card.append(actions);
  }
  solResults.append(card);
}

solExample.addEventListener("change", () => {
  editor.value = solExamples[Number(solExample.value)]?.source ?? "";
  solResults.replaceChildren();
});

const fmt = (secs: number) => (secs < 10 ? secs.toFixed(2) : secs.toFixed(1)) + "s";

function renderProgress(stats: Stats, running: boolean, elapsed: number, phase = "Starting…") {
  const done = testsDone(stats);
  const current = stats.tests.at(-1);
  const checking = running && current && current.secs === undefined ? current : undefined;
  const bar = el("div", "bar");
  const fill = el("div", "fill");
  fill.style.width = stats.total ? `${(100 * done) / stats.total}%` : "0";
  const label = checking
    ? `${checking.name.split("(")[0]} · ${done + 1} of ${stats.total || "?"}`
    : running ? phase : `Done: ${done} of ${stats.total} functions`;
  const name = el("span", "label", label);
  if (checking) name.title = checking.name;
  bar.append(fill, name);
  bar.classList.toggle("busy", running);
  const counters = el("dl", "counters");
  const add = (k: string, v: string) => {
    const item = el("div");
    item.append(el("dt", undefined, k), el("dd", undefined, v));
    counters.append(item);
  };
  add("Functions", `${done} / ${stats.total || "?"}`);
  add("Paths", String(stats.paths));
  add("Branches", String(stats.forks));
  add("SMT queries", stats.queriesDone + (stats.queriesInFlight ? ` (+${stats.queriesInFlight} running)` : ""));
  add("Solver time", fmt(stats.solveSecs));
  add("Elapsed", fmt(elapsed));
  solProgress.replaceChildren(bar, counters);
  solProgress.hidden = false;
}

function renderStats(stats: Stats) {
  if (!stats.tests.length) return;
  const card = el("article", "card stats");
  card.append(el("h3", undefined, "Statistics"));
  const table = el("table");
  const row = (cells: string[], tag: "th" | "td" = "td") => {
    const tr = el("tr");
    cells.forEach((c, i) => tr.append(el(tag, i ? "num" : undefined, c)));
    return tr;
  };
  table.append(row(["Function", "Paths", "Branches", "SMT queries", "Solver time", "Time", "Counterexamples"], "th"));
  for (const t of stats.tests) {
    const tr = row([t.name.split("(")[0]!, String(t.paths), String(t.forks), String(t.queries), fmt(t.solveSecs), fmt(t.secs ?? 0), String(t.cex)]);
    tr.firstElementChild!.setAttribute("title", t.name);
    table.append(tr);
  }
  // scrolls by itself on a narrow screen rather than widening the page
  const wrap = el("div", "table-wrap");
  wrap.append(table);
  card.append(wrap);
  const results = Object.entries(stats.results).map(([r, n]) => `${n} ${r}`).join(", ");
  card.append(el("p", "muted", `${stats.queriesDone} SMT queries${results ? `: ${results}` : ""}, ${fmt(stats.solveSecs)} in the solver, ${fmt(stats.elapsed)} in all.`));
  solResults.append(card);
}

solForm.addEventListener("submit", async (e) => {
  e.preventDefault();
  prove.disabled = true;
  solResults.replaceChildren();
  solProgress.hidden = true;
  failingLines = [];
  const started = performance.now();
  const secs = () => ((performance.now() - started) / 1000).toFixed(2);
  const stats = newStats();
  const stdout: string[] = [];
  const showTests = () => {
    solResults.replaceChildren();
    failingLines = [];
    const tests = parseTestOutput(stdout.join("\n"));
    tests.forEach(renderTest);
    return tests;
  };
  let frame = 0;
  const elapsed = () => (performance.now() - started) / 1000;
  let phase = "Compiling…";
  // hevm reports nothing while the solver works, the clock keeps going
  const clock = setInterval(() => renderProgress(stats, true, elapsed(), phase), 250);
  renderProgress(stats, true, 0, phase);
  const onStream = (m: WorkerStream) => {
    if ("stdout" in m) {
      stdout.push(m.stdout);
      onStdout(stats, m.stdout);
    } else {
      onProgress(stats, m.progress);
    }
    // at most once a frame, however fast hevm reports
    frame ||= requestAnimationFrame(() => {
      frame = 0;
      renderProgress(stats, true, elapsed(), phase);
      showTests();
    });
  };
  try {
    solStatus.textContent = "Compiling…";
    const project = await compile([{ path: sourcePath, content: editor.value }]);
    lastProject = project;
    const errors = project.errors.filter((x) => x.severity === "error");
    if (errors.length) {
      solStatus.textContent = `Compilation failed — ${secs()}s`;
      clearInterval(clock);
      solProgress.hidden = true;
      renderErrors(errors);
      return;
    }
    solStatus.textContent = "Proving…";
    phase = "Starting hevm…";
    renderProgress(stats, true, elapsed(), phase);
    const run = await runHevm(["test", "--root", "/", "--progress-log", progressPath], project.files, onStream);
    cancelAnimationFrame(frame);
    clearInterval(clock);
    stdout.splice(0, stdout.length, ...run.stdout.split("\n"));
    renderProgress(stats, false, elapsed());
    const tests = showTests();
    const failed = tests.filter((t) => t.status === "fail").length;
    solStatus.textContent = tests.length
      ? `${tests.length - failed} passed, ${failed} failed — ${secs()}s`
      : `No prove_ functions found — ${secs()}s`;
    renderStats(stats);
    if (!tests.length && run.exitCode !== 0) {
      solResults.append(el("pre", "card fail", stripAnsi(run.stderr || run.stdout)));
    }
  } catch (err) {
    clearInterval(clock);
    solProgress.hidden = true;
    solStatus.textContent = "";
    solResults.append(el("pre", "card fail", String(err)));
  } finally {
    clearInterval(clock);
    editor.markFailing(failingLines);
    prove.disabled = false;
  }
});

solExamples.forEach((ex, i) => solExample.add(new Option(ex.name, String(i))));
const editor = new SolidityEditor($("source"), solExamples[0]!.source);
let failingLines: number[] = [];
let lastProject: Project | undefined;

// --- bytecode ---

const form = $<HTMLFormElement>("form");
const example = $<HTMLSelectElement>("example");
const code = $<HTMLTextAreaElement>("code");
const calldata = $<HTMLInputElement>("calldata");
const sig = $<HTMLInputElement>("sig");
const run = $<HTMLButtonElement>("run");
const status = $<HTMLElement>("status");
const outcome = $<HTMLElement>("outcome");

function mode(): Mode {
  return (form.elements.namedItem("mode") as RadioNodeList).value as Mode;
}

function showMode() {
  document.body.dataset.mode = mode();
}

function load(req: Request) {
  (form.elements.namedItem("mode") as RadioNodeList).value = req.mode;
  code.value = req.code;
  calldata.value = req.calldata ?? "";
  sig.value = req.sig ?? "";
  showMode();
}

function render(o: Outcome) {
  outcome.className = `outcome ${o.kind}`;
  switch (o.kind) {
    case "return":
    case "revert":
      outcome.replaceChildren(el("h2", undefined, o.kind === "return" ? "Returned" : "Reverted"), el("code", undefined, o.data));
      break;
    case "safe":
      outcome.replaceChildren(el("h2", undefined, "Proved"), el("p", undefined, "No input reaches a failure."));
      break;
    case "counterexamples":
      outcome.replaceChildren(
        el("h2", undefined, `${o.calldata.length} counterexample${o.calldata.length === 1 ? "" : "s"}`),
        ...o.calldata.map((c) => el("code", undefined, c)),
      );
      break;
    case "error":
      outcome.replaceChildren(el("h2", undefined, "Error"), el("pre", undefined, o.message));
      break;
  }
}

form.addEventListener("change", (e) => {
  if ((e.target as HTMLElement).getAttribute("name") === "mode") showMode();
});

example.addEventListener("change", () => {
  const ex = examples[Number(example.value)];
  if (ex) load(ex.request);
});

form.addEventListener("submit", async (e) => {
  e.preventDefault();
  const req: Request = { mode: mode(), code: code.value, calldata: calldata.value, sig: sig.value };
  let args: string[];
  try {
    args = buildArgs(req);
  } catch (err) {
    render({ kind: "error", message: (err as Error).message });
    return;
  }
  run.disabled = true;
  status.textContent = req.mode === "symbolic" ? "Exploring all paths…" : "Running…";
  const started = performance.now();
  try {
    const res = await runHevm(args);
    status.textContent = `hevm ${args.join(" ")} — ${((performance.now() - started) / 1000).toFixed(2)}s, exit code ${res.exitCode}`;
    render(parseOutcome(req.mode, res));
  } catch (err) {
    status.textContent = "";
    render({ kind: "error", message: String(err) });
  } finally {
    run.disabled = false;
  }
});

examples.forEach((ex, i) => example.add(new Option(ex.name, String(i))));
load(examples[0]!.request);

setupEquivalence({
  openInBytecode(code, calldata) {
    load({ mode: "exec", code, calldata });
    outcome.replaceChildren();
    showTab("bytecode");
  },
});
