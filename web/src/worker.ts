import { runHevm, type RunResult } from "./hevm";

export interface WorkerRequest {
  id: number;
  args: string[];
  wasmUrl: string;
}

export type WorkerResponse = { id: number } & ({ ok: true; result: RunResult } | { ok: false; error: string });

let module: Promise<WebAssembly.Module> | undefined;

self.onmessage = async (e: MessageEvent<WorkerRequest>) => {
  const { id, args, wasmUrl } = e.data;
  try {
    module ??= WebAssembly.compileStreaming(fetch(wasmUrl));
    const result = await runHevm(await module, args);
    self.postMessage({ id, ok: true, result } satisfies WorkerResponse);
  } catch (err) {
    module = undefined;
    self.postMessage({ id, ok: false, error: String(err) } satisfies WorkerResponse);
  }
};
