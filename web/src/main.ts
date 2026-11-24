import "./style.css";
import { buildArgs, parseOutcome, stripAnsi, type Files, type Mode, type Outcome, type Request, type RunResult } from "./hevm";
import { examples } from "./examples";
import { describeResult, parseTestOutput, type TestResult } from "./results";
import { solExamples } from "./solExamples";
import type { CompileError, Project, Source } from "./solc";
import type { WorkerRequest, WorkerResponse } from "./worker";

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
const pending = new Map<number, (r: WorkerResponse) => void>();
worker.onmessage = (e: MessageEvent<WorkerResponse>) => {
  pending.get(e.data.id)?.(e.data);
  pending.delete(e.data.id);
};

type Body = { kind: "hevm"; args: string[]; files?: Files } | { kind: "compile"; sources: Source[] };

function call(body: Body): Promise<WorkerResponse> {
  const id = nextId++;
  return new Promise((resolve) => {
    pending.set(id, resolve);
    worker.postMessage({ id, ...urls, ...body } as WorkerRequest);
  });
}

async function runHevm(args: string[], files?: Files): Promise<RunResult> {
  const res = await call({ kind: "hevm", args, files });
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
const source = $<HTMLTextAreaElement>("source");
const prove = $<HTMLButtonElement>("prove");
const solStatus = $<HTMLElement>("sol-status");
const solResults = $<HTMLElement>("sol-results");

function el<K extends keyof HTMLElementTagNameMap>(tag: K, cls?: string, text?: string) {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
}

/** A few lines of the source around a line, which is highlighted from the column on */
function excerpt(text: string, line: number, column: number, length: number) {
  const lines = text.split("\n");
  const pre = el("pre", "excerpt");
  for (let n = Math.max(1, line - 2); n <= Math.min(lines.length, line + 2); n++) {
    const row = el("div", n === line ? "hit" : undefined);
    row.append(el("span", "ln", String(n)));
    const content = lines[n - 1] ?? "";
    if (n === line) {
      row.append(
        content.slice(0, column - 1),
        el("mark", undefined, content.slice(column - 1, column - 1 + length)),
        content.slice(column - 1 + length),
      );
    } else {
      row.append(content);
    }
    pre.append(row);
  }
  pre.addEventListener("click", () => selectLine(line));
  pre.title = "Show in the editor";
  return pre;
}

function selectLine(line: number) {
  const lines = source.value.split("\n");
  const start = lines.slice(0, line - 1).reduce((n, l) => n + l.length + 1, 0);
  source.focus();
  source.setSelectionRange(start, start + (lines[line - 1]?.length ?? 0));
  const lineHeight = parseFloat(getComputedStyle(source).lineHeight) || 20;
  source.scrollTop = Math.max(0, (line - 4) * lineHeight);
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
      const { line, column } = lineCol(source.value, e.start);
      card.append(excerpt(source.value, line, column, Math.max(1, e.end - e.start)));
    }
    solResults.append(card);
  }
}

function renderTest(t: TestResult) {
  const card = el("article", `card ${t.status}`);
  const head = el("h3");
  head.append(el("span", `badge ${t.status}`, t.status === "pass" ? "PASS" : "FAIL"), ` ${t.name}`);
  card.append(head);
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
      card.append(el("p", "where", `Fails at line ${c.at.line}:`));
      card.append(excerpt(source.value, c.at.line, c.at.column, c.at.code.length));
    } else if (c.at) {
      card.append(el("p", "where", `Fails at ${c.at.file}:${c.at.line}: ${c.at.code}`));
    }
  }
  for (const n of t.notes) card.append(el("p", "muted", n));
  solResults.append(card);
}

solExample.addEventListener("change", () => {
  source.value = solExamples[Number(solExample.value)]?.source ?? "";
  solResults.replaceChildren();
});

source.addEventListener("keydown", (e) => {
  if (e.key === "Tab") {
    e.preventDefault();
    source.setRangeText("    ", source.selectionStart, source.selectionEnd, "end");
  }
});

solForm.addEventListener("submit", async (e) => {
  e.preventDefault();
  prove.disabled = true;
  solResults.replaceChildren();
  const started = performance.now();
  const secs = () => ((performance.now() - started) / 1000).toFixed(2);
  try {
    solStatus.textContent = "Compiling…";
    const project = await compile([{ path: sourcePath, content: source.value }]);
    const errors = project.errors.filter((x) => x.severity === "error");
    if (errors.length) {
      solStatus.textContent = `Compilation failed — ${secs()}s`;
      renderErrors(errors);
      return;
    }
    solStatus.textContent = "Proving…";
    const run = await runHevm(["test", "--root", "/"], project.files);
    const tests = parseTestOutput(run.stdout);
    const failed = tests.filter((t) => t.status === "fail").length;
    solStatus.textContent = tests.length
      ? `${tests.length - failed} passed, ${failed} failed — ${secs()}s`
      : `No prove_ functions found — ${secs()}s`;
    tests.forEach(renderTest);
    if (!tests.length && run.exitCode !== 0) {
      solResults.append(el("pre", "card fail", stripAnsi(run.stderr || run.stdout)));
    }
  } catch (err) {
    solStatus.textContent = "";
    solResults.append(el("pre", "card fail", String(err)));
  } finally {
    prove.disabled = false;
  }
});

solExamples.forEach((ex, i) => solExample.add(new Option(ex.name, String(i))));
source.value = solExamples[0]!.source;

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
