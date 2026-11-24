// The page's side of the worker, which compiles and runs hevm
import { stripAnsi, type Files, type RunResult } from "./hevm";
import type { CompileSettings, Project, Source } from "./solc";
import type { WorkerRequest, WorkerResponse, WorkerStream } from "./worker";

const worker = new Worker(new URL("./worker.ts", import.meta.url), { type: "module" });
// relative to the page: the worker's own URL is under assets/
const urls = {
  wasmUrl: new URL("hevm.wasm", document.baseURI).href,
  solcUrl: new URL("soljson.js", document.baseURI).href,
};
let nextId = 0;
export type OnStream = (m: WorkerStream) => void;
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

type Body =
  | { kind: "hevm"; args: string[]; files?: Files; stream?: boolean }
  | { kind: "compile"; sources: Source[]; settings?: CompileSettings };

function call(body: Body, onStream?: OnStream): Promise<WorkerResponse> {
  const id = nextId++;
  return new Promise((resolve) => {
    pending.set(id, { resolve, onStream });
    worker.postMessage({ id, ...urls, ...body } as WorkerRequest);
  });
}

/** Gets the output of each hevm run, for the page's "hevm output" panel */
let outputSink: (text: string) => void = () => {};
export function onHevmOutput(sink: (text: string) => void) {
  outputSink = sink;
}

export async function runHevm(args: string[], files?: Files, onStream?: OnStream): Promise<RunResult> {
  const res = await call({ kind: "hevm", args, files, stream: onStream !== undefined }, onStream);
  if (!res.ok) throw new Error(res.error);
  if (!("result" in res)) throw new Error("unexpected worker reply");
  outputSink(stripAnsi([res.result.stdout, res.result.stderr].filter(Boolean).join("\n")));
  return res.result;
}

export async function compile(sources: Source[], settings?: CompileSettings): Promise<Project> {
  const res = await call({ kind: "compile", sources, ...(settings && { settings }) });
  if (!res.ok) throw new Error(res.error);
  if (!("project" in res)) throw new Error("unexpected worker reply");
  return res.project;
}
