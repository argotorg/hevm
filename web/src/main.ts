import "./style.css";
import { buildArgs, parseOutcome, progressPath, stripAnsi, type Files, type Mode, type Outcome, type Request, type RunResult } from "./hevm";
import { examples } from "./examples";
import { SolidityEditor } from "./editor";
import { segments, tokens } from "./highlight";
import { newStats, onProgress, onStdout, testsDone, type Stats } from "./progress";
import { describeResult, parseTestOutput, type TestResult } from "./results";
import { solExamples } from "./solExamples";
import type { CompileError, Project, Source } from "./solc";
import type { WorkerRequest, WorkerResponse, WorkerStream } from "./worker";

const $ = <T extends HTMLElement>(id: string) => document.getElementById(id) as T;
const log = $<HTMLElement>("log");
const sourcePath = "src/Main.sol";

// --- the worker, which compiles and runs hevm ---

const worker = new Worker(new URL("./worker.ts", import.meta.url), { type: "module" });
// relative to the page: the worker's own URL is under assets/
const urls = {
  wasmUrl: new URL("hevm.wasm", document.baseURI).href,
  solcUrl: new URL("soljson.js", document.baseURI).href,
};
let nextId = 0;
type OnStream = (m: WorkerStream) => void;
const pending = new Map<number, { resolve: (r: WorkerResponse) => void; onStream?: OnStream }>();
worker.onmessage = (e: MessageEvent<WorkerResponse | WorkerStream>) => {
  const p = pending.get(e.data.id);
  if ("stream" in e.data) {
    p?.onStream?.(e.data);
  } else {
    p?.resolve(e.data);
    pending.delete(e.data.id);
  }
};

type Body = { kind: "hevm"; args: string[]; files?: Files; stream?: boolean } | { kind: "compile"; sources: Source[] };

function call(body: Body, onStream?: OnStream): Promise<WorkerResponse> {
  const id = nextId++;
  return new Promise((resolve) => {
    pending.set(id, { resolve, onStream });
    worker.postMessage({ id, ...urls, ...body } as WorkerRequest);
  });
}

async function runHevm(args: string[], files?: Files, onStream?: OnStream): Promise<RunResult> {
  const res = await call({ kind: "hevm", args, files, stream: onStream !== undefined }, onStream);
  if (!res.ok) throw new Error(res.error);
  if (!("result" in res)) throw new Error("unexpected worker reply");
  log.textContent = stripAnsi([res.result.stdout, res.result.stderr].filter(Boolean).join("\n"));
  return res.result;
}

async function compile(sources: Source[]): Promise<Project> {
  const res = await call({ kind: "compile", sources });
  if (!res.ok) throw new Error(res.error);
  if (!("project" in res)) throw new Error("unexpected worker reply");
  return res.project;
}

// --- tabs ---

for (const tab of document.querySelectorAll<HTMLButtonElement>(".tabs button")) {
  tab.addEventListener("click", () => {
    document.body.dataset.tab = tab.dataset.tab;
  });
}

// --- Solidity ---

const solForm = $<HTMLFormElement>("sol-form");
const solExample = $<HTMLSelectElement>("sol-example");
const prove = $<HTMLButtonElement>("prove");
const solStatus = $<HTMLElement>("sol-status");
const solResults = $<HTMLElement>("sol-results");
const solProgress = $<HTMLElement>("sol-progress");

function el<K extends keyof HTMLElementTagNameMap>(tag: K, cls?: string, text?: string) {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
}

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
  }
  for (const n of t.notes) card.append(el("p", "muted", n));
  solResults.append(card);
}

solExample.addEventListener("change", () => {
  editor.value = solExamples[Number(solExample.value)]?.source ?? "";
  solResults.replaceChildren();
});

const fmt = (secs: number) => (secs < 10 ? secs.toFixed(2) : secs.toFixed(1)) + "s";

function renderProgress(stats: Stats, running: boolean, elapsed: number) {
  const done = testsDone(stats);
  const current = stats.tests.at(-1);
  const bar = el("div", "bar");
  const fill = el("div", "fill");
  fill.style.width = stats.total ? `${(100 * done) / stats.total}%` : "0";
  bar.append(fill);
  bar.classList.toggle("busy", running);
  const what = running && current && current.secs === undefined
    ? `Checking ${current.name}`
    : running ? "Starting…" : "Done";
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
  solProgress.replaceChildren(el("p", "what", what), bar, counters);
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
  // hevm reports nothing while the solver works, the clock keeps going
  const clock = setInterval(() => renderProgress(stats, true, elapsed()), 250);
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
      renderProgress(stats, true, elapsed());
      showTests();
    });
  };
  try {
    solStatus.textContent = "Compiling…";
    const project = await compile([{ path: sourcePath, content: editor.value }]);
    const errors = project.errors.filter((x) => x.severity === "error");
    if (errors.length) {
      solStatus.textContent = `Compilation failed — ${secs()}s`;
      clearInterval(clock);
      solProgress.hidden = true;
      renderErrors(errors);
      return;
    }
    solStatus.textContent = "Proving…";
    renderProgress(stats, true, elapsed());
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
