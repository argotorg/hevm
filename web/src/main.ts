import "./style.css";
import { buildArgs, parseOutcome, stripAnsi, type Mode, type Outcome, type Request } from "./hevm";
import { examples } from "./examples";
import type { WorkerRequest, WorkerResponse } from "./worker";

const $ = <T extends HTMLElement>(id: string) => document.getElementById(id) as T;

const form = $<HTMLFormElement>("form");
const example = $<HTMLSelectElement>("example");
const code = $<HTMLTextAreaElement>("code");
const calldata = $<HTMLInputElement>("calldata");
const sig = $<HTMLInputElement>("sig");
const run = $<HTMLButtonElement>("run");
const status = $<HTMLElement>("status");
const outcome = $<HTMLElement>("outcome");
const log = $<HTMLElement>("log");

const worker = new Worker(new URL("./worker.ts", import.meta.url), { type: "module" });
// relative to the page: the worker's own URL is under assets/
const wasmUrl = new URL("hevm.wasm", document.baseURI).href;
let nextId = 0;
const pending = new Map<number, (r: WorkerResponse) => void>();
worker.onmessage = (e: MessageEvent<WorkerResponse>) => {
  pending.get(e.data.id)?.(e.data);
  pending.delete(e.data.id);
};

function call(args: string[]): Promise<WorkerResponse> {
  const id = nextId++;
  return new Promise((resolve) => {
    pending.set(id, resolve);
    worker.postMessage({ id, args, wasmUrl } satisfies WorkerRequest);
  });
}

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
      outcome.innerHTML = `<h2>Returned</h2><code></code>`;
      outcome.querySelector("code")!.textContent = o.data;
      break;
    case "revert":
      outcome.innerHTML = `<h2>Reverted</h2><code></code>`;
      outcome.querySelector("code")!.textContent = o.data;
      break;
    case "safe":
      outcome.innerHTML = `<h2>Proved</h2><p>No input reaches a failure.</p>`;
      break;
    case "counterexamples":
      outcome.innerHTML = `<h2>${o.calldata.length} counterexample${o.calldata.length === 1 ? "" : "s"}</h2>`;
      for (const c of o.calldata) {
        const el = document.createElement("code");
        el.textContent = c;
        outcome.append(el);
      }
      break;
    case "error":
      outcome.innerHTML = `<h2>Error</h2><pre></pre>`;
      outcome.querySelector("pre")!.textContent = o.message;
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
  const res = await call(args);
  const secs = ((performance.now() - started) / 1000).toFixed(2);
  run.disabled = false;
  if (!res.ok) {
    status.textContent = "";
    render({ kind: "error", message: res.error });
    return;
  }
  status.textContent = `hevm ${args.join(" ")} — ${secs}s, exit code ${res.result.exitCode}`;
  render(parseOutcome(req.mode, res.result));
  log.textContent = stripAnsi([res.result.stdout, res.result.stderr].filter(Boolean).join("\n"));
});

examples.forEach((ex, i) => example.add(new Option(ex.name, String(i))));
load(examples[0]!.request);
