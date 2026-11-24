// Runs a debugging session on hevm-web.wasm and answers the debugger's API requests to it.
import type { Files } from "./hevm";
import { Reactor, type JsffiGlue } from "./reactor";

export type DebugRequest = { id: number } & (
  | { kind: "start"; wasmUrl: string; glueUrl: string; files: Files; args: string[] }
  | { kind: "api"; method: "GET" | "POST"; path: string; body?: string }
);

export type DebugResponse = { id: number } & ({ ok: true; status: number; text: string } | { ok: false; error: string });

let module: Promise<WebAssembly.Module> | undefined;
let glue: Promise<JsffiGlue> | undefined;
let reactor: Reactor | undefined;

async function start(req: Extract<DebugRequest, { kind: "start" }>): Promise<DebugResponse> {
  module ??= WebAssembly.compileStreaming(fetch(req.wasmUrl));
  glue ??= import(/* @vite-ignore */ req.glueUrl).then((m: { default: JsffiGlue }) => m.default);
  const r = await Reactor.start(await module, await glue, { files: req.files });
  let exitCode: number | undefined;
  void r.main(req.args).then((c) => (exitCode = c));
  // the session's routes are there once hevm has set the run up, unless it stopped first
  for (;;) {
    const state = await r.api("GET", "/state");
    if (state.status !== 404) break;
    if (exitCode !== undefined) {
      return { id: req.id, ok: false, error: [...r.stdout, ...r.stderr].join("\n") || `hevm exited with ${exitCode}` };
    }
    await new Promise((resolve) => setTimeout(resolve, 20));
  }
  reactor = r;
  return { id: req.id, ok: true, status: 200, text: "" };
}

self.onmessage = async (e: MessageEvent<DebugRequest>) => {
  const req = e.data;
  let res: DebugResponse;
  try {
    if (req.kind === "start") {
      res = await start(req);
    } else if (!reactor) {
      res = { id: req.id, ok: false, error: "no debugging session" };
    } else {
      const r = await reactor.api(req.method, req.path, req.body);
      res = { id: req.id, ok: true, status: r.status, text: r.content };
    }
  } catch (err) {
    res = { id: req.id, ok: false, error: String(err) };
  }
  self.postMessage(res);
};
