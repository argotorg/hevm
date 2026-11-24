import "./style.css";
import { buildArgs, parseOutcome, progressPath, stripAnsi, type Mode, type Outcome, type Request } from "./hevm";
import { compile, onHevmOutput, runHevm } from "./client";
import { $, button, el } from "./dom";
import { setupEquivalence } from "./eqTab";
import { decodeShare, encodeShare, type Shared } from "./share";
import { examples } from "./examples";
import { segments, tokens } from "./highlight";
import { newStats, onProgress, onStdout, testsDone, type Stats } from "./progress";
import { describeResult, parseTestOutput, readableNumbers, type TestResult } from "./results";
import { solExamples } from "./solExamples";
import { artifactPath, type CompileError, type Project } from "./solc";
import { fetchVerified } from "./sourcify";
import { Workspace, setupSourcify } from "./workspace";
import type { DebugSession } from "./debugger-page";
import type { WorkerStream } from "./worker";

const log = $<HTMLElement>("log");
onHevmOutput((text) => (log.textContent = text));

// --- tabs ---

function showTab(name: string) {
  if (name === "sol" || name === "sourcify") switchSol(name);
  document.body.dataset.tab = name;
}

for (const tab of document.querySelectorAll<HTMLButtonElement>(".tabs button")) {
  tab.addEventListener("click", () => showTab(tab.dataset.tab!));
}

// --- the debugger tab, a page of its own in an iframe ---

const debugFrame = $<HTMLIFrameElement>("debugger");
const debugCaption = $<HTMLElement>("debug-caption");
const debugTab = document.querySelector<HTMLButtonElement>('.tabs [data-tab="debug"]')!;
let debugSession: DebugSession | undefined;

window.addEventListener("message", (e) => {
  if (e.source === debugFrame.contentWindow && e.data?.kind === "hevm-debugger-ready" && debugSession) {
    debugFrame.contentWindow!.postMessage(debugSession, "*");
  }
});

// the tab shows once there is something to debug
function openDebugger(project: Project, args: string[], caption: string) {
  debugSession = { kind: "hevm-debug", files: project.files, args };
  debugCaption.textContent = caption;
  debugTab.hidden = false;
  // a fresh page for each session
  debugFrame.src = `debugger/index.html?session=${Date.now()}`;
  showTab("debug");
}

/** The runtime code of a compiled contract, e.g. "src/Main.sol:Example" */
function runtimeCode(project: Project, contract: string): string | undefined {
  const [path, name] = contract.split(":");
  const artifact = project.files[artifactPath(path!, name!)];
  return artifact ? (JSON.parse(artifact) as { deployedBytecode: { object: string } }).deployedBytecode.object : undefined;
}

function openInBytecode(project: Project, t: TestResult, calldata?: string) {
  const code = runtimeCode(project, t.contract);
  if (!code) return;
  load(calldata ? { mode: "exec", code, calldata } : { mode: "symbolic", code, sig: t.name });
  outcome.replaceChildren();
  showTab("bytecode");
}

// --- Solidity ---

const solForm = $<HTMLFormElement>("sol-form");
const solExample = $<HTMLSelectElement>("sol-example");
const prove = $<HTMLButtonElement>("prove");
// the Solidity and Sourcify tabs share the form, each with its project and what hevm found
type SolTab = "sol" | "sourcify";
interface SolOutput {
  status: HTMLElement;
  results: HTMLElement;
  progress: HTMLElement;
  /** lines where a counterexample or an error is, per file */
  failing: Map<string, number[]>;
}
const outputs: Record<SolTab, SolOutput> = {
  sol: { status: $("sol-status"), results: $("sol-results"), progress: $("sol-progress"), failing: new Map() },
  sourcify: { status: $("sf-status"), results: $("sf-results"), progress: $("sf-progress"), failing: new Map() },
};
let solTab: SolTab = "sol";
const solStatus = outputs.sol.status;
const solResults = outputs.sol.results;
const solProgress = outputs.sol.progress;
const saved: Partial<Record<SolTab, ReturnType<Workspace["snapshot"]>>> = {};

function switchSol(to: SolTab) {
  if (to === solTab) return;
  saved[solTab] = workspace.snapshot();
  const back = saved[to];
  if (back) workspace.restore(back);
  else workspace.clear();
  solTab = to;
  editor.markFailing(outputs[to].failing);
}

function fail(o: SolOutput, file: string, line: number) {
  o.failing.set(file, [...(o.failing.get(file) ?? []), line]);
}

/** A few highlighted lines of a file around a line, marked from the column on */
function excerpt(file: string, line: number, column: number, length: number) {
  const text = editor.text(file) ?? "";
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
  pre.addEventListener("click", () => editor.selectLine(file, line));
  pre.title = "Show in the editor";
  return pre;
}

function lineCol(text: string, offset: number) {
  const before = text.slice(0, offset);
  const line = before.split("\n").length;
  return { line, column: offset - before.lastIndexOf("\n") };
}

function renderErrors(o: SolOutput, errors: CompileError[]) {
  for (const e of errors) {
    const card = el("article", `card ${e.severity === "error" ? "fail" : "note"}`);
    card.append(el("h3", undefined, `${e.severity === "error" ? "Error" : "Warning"}: ${e.message}`));
    if (e.file && editor.has(e.file) && e.start !== undefined && e.end !== undefined) {
      const { line, column } = lineCol(editor.text(e.file)!, e.start);
      fail(o, e.file, line);
      if (workspace.visible().length > 1) card.append(el("p", "where", e.file));
      card.append(excerpt(e.file, line, column, Math.max(1, e.end - e.start)));
    }
    o.results.append(card);
  }
}

function renderTest(o: SolOutput, project: Project, t: TestResult) {
  const card = el("article", `card ${t.status}`);
  const head = el("h3");
  head.append(el("span", `badge ${t.status}`, t.status.toUpperCase()), ` ${t.name}`);
  card.append(head);
  if (t.status === "running" && !t.counterexamples.length) card.append(el("p", "muted", "Checking…"));
  const invariant = t.name.startsWith("invariant_");
  if (t.status === "pass" && !t.counterexamples.length) {
    card.append(el("p", "muted", invariant
      ? `No sequence of calls breaks it${t.detail ? `: ${t.detail}` : ""}.`
      : "No input breaks it."));
  }
  const debugArgs = ["test", "--root", "/", "--match", `^${t.name.split("(")[0]}$`, "--interactive"];
  for (const c of t.counterexamples) {
    const dl = el("dl");
    if (c.calls) {
      const calls = el("ol", "calls");
      for (const call of c.calls) calls.append(el("li", "mono", readableNumbers(call)));
      const dd = el("dd");
      dd.append(calls);
      dl.append(el("dt", undefined, "Calls"), dd, el("dt", undefined, "Then"), el("dd", "mono", c.calldata));
    } else {
      dl.append(el("dt", undefined, "Counterexample"), el("dd", "mono", readableNumbers(c.calldata)));
    }
    dl.append(el("dt", undefined, "Result"), el("dd", undefined, describeResult(c.result)));
    if (c.validated === false) dl.append(el("dt"), el("dd", "muted", "could not be reproduced concretely"));
    card.append(dl);
    if (c.at && editor.has(c.at.file)) {
      fail(o, c.at.file, c.at.line);
      card.append(el("p", "where", workspace.visible().length > 1 ? `Fails at ${c.at.file}, line ${c.at.line}:` : `Fails at line ${c.at.line}:`));
      card.append(excerpt(c.at.file, c.at.line, c.at.column, c.at.code.length));
    } else if (c.at) {
      card.append(el("p", "where", `Fails at ${c.at.file}:${c.at.line}: ${c.at.code}`));
    }
    const raw = c.raw;
    // the debugger and the Bytecode tab run one call, not a sequence
    if (raw && !invariant) {
      const actions = el("div", "card-actions");
      actions.append(
        button("Replay in debugger", () => openDebugger(project, [...debugArgs, "--calldata", raw],
          `Replaying ${readableNumbers(c.calldata)}: step through it, or press Continue to run to where it fails.`)),
        button("Open in Bytecode tab", () => openInBytecode(project, t, raw)),
      );
      card.append(actions);
    }
  }
  for (const n of t.notes) card.append(el("p", "muted", n));
  if (t.status !== "running" && !invariant) {
    const actions = el("div", "card-actions");
    actions.append(button("Debug symbolically", () => openDebugger(project, debugArgs,
      `Debugging ${t.name.split("(")[0]} for all inputs at once: at each branch that depends on them, you pick the side to follow.`)));
    if (!t.counterexamples.length) actions.append(button("Open in Bytecode tab", () => openInBytecode(project, t)));
    card.append(actions);
  }
  o.results.append(card);
}

const solStory = $<HTMLElement>("sol-story");

function showStory() {
  const story = solExample.value === "" ? undefined : solExamples[Number(solExample.value)]?.story;
  solStory.textContent = story ?? "";
  solStory.hidden = !story;
}

solExample.addEventListener("change", () => {
  workspace.loadExample(solExamples[Number(solExample.value)]?.source ?? "");
  showStory();
  solResults.replaceChildren();
});

const fmt = (secs: number) => (secs < 10 ? secs.toFixed(2) : secs.toFixed(1)) + "s";

function renderProgress(o: SolOutput, stats: Stats, running: boolean, elapsed: number, phase = "Starting…") {
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
  o.progress.replaceChildren(bar, counters);
  o.progress.hidden = false;
}

function renderStats(o: SolOutput, stats: Stats) {
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
  o.results.append(card);
}

solForm.addEventListener("submit", async (e) => {
  e.preventDefault();
  if (workspace.empty()) return;
  prove.disabled = true;
  // the output of the tab the run started in, wherever one goes meanwhile
  const runTab = solTab;
  const o = outputs[runTab];
  o.results.replaceChildren();
  o.progress.hidden = true;
  o.failing = new Map();
  let project: Project | undefined;
  const started = performance.now();
  const secs = () => ((performance.now() - started) / 1000).toFixed(2);
  const stats = newStats();
  const stdout: string[] = [];
  const showTests = () => {
    o.results.replaceChildren();
    o.failing = new Map();
    const tests = parseTestOutput(stdout.join("\n"));
    for (const t of tests) renderTest(o, project!, t);
    return tests;
  };
  let frame = 0;
  const elapsed = () => (performance.now() - started) / 1000;
  let phase = "Compiling…";
  // hevm reports nothing while the solver works, the clock keeps going
  const clock = setInterval(() => renderProgress(o, stats, true, elapsed(), phase), 250);
  renderProgress(o, stats, true, 0, phase);
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
      renderProgress(o, stats, true, elapsed(), phase);
      showTests();
    });
  };
  try {
    const version = workspace.project.version;
    o.status.textContent = version ? `Compiling with solc ${version.split("+")[0]}…` : "Compiling…";
    project = await compile(workspace.sources(), workspace.settings(), version);
    const errors = project.errors.filter((x) => x.severity === "error");
    if (errors.length) {
      o.status.textContent = `Compilation failed — ${secs()}s`;
      clearInterval(clock);
      o.progress.hidden = true;
      renderErrors(o, errors);
      return;
    }
    o.status.textContent = "Proving…";
    phase = "Starting hevm…";
    renderProgress(o, stats, true, elapsed(), phase);
    const run = await runHevm(["test", "--root", "/", "--progress-log", progressPath], project.files, onStream);
    cancelAnimationFrame(frame);
    clearInterval(clock);
    stdout.splice(0, stdout.length, ...run.stdout.split("\n"));
    renderProgress(o, stats, false, elapsed());
    const tests = showTests();
    const failed = tests.filter((t) => t.status === "fail").length;
    o.status.textContent = tests.length
      ? `${tests.length - failed} passed, ${failed} failed — ${secs()}s`
      : `No prove_ functions found — ${secs()}s`;
    renderStats(o, stats);
    if (!tests.length && run.exitCode !== 0) {
      o.results.append(el("pre", "card fail", stripAnsi(run.stderr || run.stdout)));
    }
  } catch (err) {
    clearInterval(clock);
    o.progress.hidden = true;
    o.status.textContent = "";
    o.results.append(el("pre", "card fail", String(err)));
  } finally {
    clearInterval(clock);
    if (solTab === runTab) editor.markFailing(o.failing);
    else if (saved[runTab]) saved[runTab]!.editor.failing = o.failing;
    prove.disabled = false;
  }
});

const groups = new Map<string, HTMLOptGroupElement>();
solExamples.forEach((ex, i) => {
  const option = new Option(ex.name, String(i));
  if (!ex.group) return solExample.add(option);
  let group = groups.get(ex.group);
  if (!group) {
    group = document.createElement("optgroup");
    group.label = ex.group;
    groups.set(ex.group, group);
    solExample.append(group);
  }
  group.append(option);
});
const defaultExample = solExamples.findIndex((e) => e.name === "Re-initializable wallet (Parity, 2017)");
solExample.value = String(defaultExample);
const workspace = new Workspace(() => {});
const editor = workspace.editor;
workspace.loadExample(solExamples[defaultExample]!.source);
showStory();
setupSourcify(workspace, () => {
  const o = outputs.sourcify;
  o.results.replaceChildren();
  o.progress.hidden = true;
  o.status.textContent = "";
  o.failing = new Map();
});

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

const eqTab = setupEquivalence({
  openInBytecode(code, calldata) {
    load({ mode: "exec", code, calldata });
    outcome.replaceChildren();
    showTab("bytecode");
  },
});

// --- links to what a tab holds ---

async function share(s: Shared, where: HTMLElement) {
  history.replaceState(null, "", `#${await encodeShare(s)}`);
  try {
    await navigator.clipboard.writeText(location.href);
    where.textContent = "Link copied";
  } catch {
    where.textContent = "The link is in the address bar";
  }
}

$("sol-share").addEventListener("click", () => {
  const { verified, version } = workspace.project;
  if (solTab === "sourcify") {
    if (!verified) return;
    const changed = version !== verified.version ? version : undefined;
    void share({ tab: "sourcify", sourcify: { chainId: verified.chainId, address: verified.address }, files: workspace.changes(),
                 ...(changed && { version: changed }) }, outputs.sourcify.status);
  } else if (workspace.single() && !version) {
    const ex = solExamples.find((e) => e.source === editor.value);
    void share(ex ? { tab: "sol", example: ex.name } : { tab: "sol", source: editor.value }, solStatus);
  } else {
    void share({ tab: "sol", files: workspace.current(), ...(version && { version }) }, solStatus);
  }
});
$("eq-share").addEventListener("click", () => void share(eqTab.shared(), $("eq-status")));
$("share").addEventListener("click", () => {
  void share({ tab: "bytecode", request: { mode: mode(), code: code.value, calldata: calldata.value, sig: sig.value } }, status);
});

async function openShared() {
  const s = await decodeShare(location.hash);
  if (!s) return;
  if (s.tab === "sourcify") {
    showTab("sourcify");
    outputs.sourcify.status.textContent = "Looking up the contract on Sourcify…";
    try {
      workspace.loadFiles(s.files, s.version, await fetchVerified(s.sourcify.chainId, s.sourcify.address));
    } catch (err) {
      outputs.sourcify.status.textContent = (err as Error).message;
      return;
    }
    outputs.sourcify.results.replaceChildren();
    solForm.requestSubmit();
  } else if (s.tab === "sol") {
    showTab("sol");
    if ("example" in s) {
      const i = solExamples.findIndex((e) => e.name === s.example);
      if (i < 0) return;
      solExample.value = String(i);
      workspace.loadExample(solExamples[i]!.source);
    } else {
      solExample.selectedIndex = -1;
      if ("source" in s) {
        workspace.loadExample(s.source);
      } else {
        workspace.loadFiles(s.files, s.version);
      }
    }
    showStory();
    solResults.replaceChildren();
    solForm.requestSubmit();
  } else if (s.tab === "eq") {
    if (!eqTab.open(s)) return;
    showTab("eq");
    eqTab.check();
  } else {
    load(s.request);
    outcome.replaceChildren();
    showTab("bytecode");
    form.requestSubmit();
  }
}

window.addEventListener("hashchange", () => void openShared());
void openShared();
