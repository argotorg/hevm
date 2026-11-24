import { runHevm, type Files, type ProgressEvent, type RunResult } from "./hevm";
import { compileProject, type Project, type Soljson, type Source } from "./solc";

export type WorkerRequest = { id: number; wasmUrl: string; solcUrl: string } & (
  | { kind: "hevm"; args: string[]; files?: Files; stream?: boolean }
  | { kind: "compile"; sources: Source[] }
);

/** Sent while hevm runs, before its WorkerResponse */
export type WorkerStream = { id: number; stream: true } & ({ stdout: string } | { progress: ProgressEvent });

export type WorkerResponse = { id: number } & (
  | { ok: true; result: RunResult }
  | { ok: true; project: Project }
  | { ok: false; error: string }
);

let hevm: Promise<WebAssembly.Module> | undefined;
let solc: Promise<Soljson> | undefined;

// soljson is a classic script that defines Module, and a module worker cannot importScripts it
async function loadSolc(url: string): Promise<Soljson> {
  const text = await (await fetch(url)).text();
  return new Function(`${text}\nreturn Module;`)() as Soljson;
}

self.onmessage = async (e: MessageEvent<WorkerRequest>) => {
  const req = e.data;
  try {
    if (req.kind === "compile") {
      solc ??= loadSolc(req.solcUrl);
      const project = compileProject(await solc, req.sources);
      self.postMessage({ id: req.id, ok: true, project } satisfies WorkerResponse);
    } else {
      hevm ??= WebAssembly.compileStreaming(fetch(req.wasmUrl));
      // posted while hevm still runs: the page gets them at once
      const post = (m: WorkerStream) => self.postMessage(m);
      const result = await runHevm(await hevm, req.args, {
        files: req.files,
        ...(req.stream && {
          onStdout: (stdout: string) => post({ id: req.id, stream: true, stdout }),
          onProgress: (progress: ProgressEvent) => post({ id: req.id, stream: true, progress }),
        }),
      });
      self.postMessage({ id: req.id, ok: true, result } satisfies WorkerResponse);
    }
  } catch (err) {
    if (req.kind === "compile") solc = undefined;
    else hevm = undefined;
    self.postMessage({ id: req.id, ok: false, error: String(err) } satisfies WorkerResponse);
  }
};
