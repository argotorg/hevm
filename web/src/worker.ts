import { runHevm, type Files, type RunResult } from "./hevm";
import { compileProject, type Project, type Soljson, type Source } from "./solc";

export type WorkerRequest = { id: number; wasmUrl: string; solcUrl: string } & (
  | { kind: "hevm"; args: string[]; files?: Files }
  | { kind: "compile"; sources: Source[] }
);

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
      const result = await runHevm(await hevm, req.args, req.files);
      self.postMessage({ id: req.id, ok: true, result } satisfies WorkerResponse);
    }
  } catch (err) {
    if (req.kind === "compile") solc = undefined;
    else hevm = undefined;
    self.postMessage({ id: req.id, ok: false, error: String(err) } satisfies WorkerResponse);
  }
};
