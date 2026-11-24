// The debugger's page. In the site's Debugger tab it debugs on hevm-web.wasm, in a worker;
// opened by itself it talks to a running `hevm ... --interactive` over HTTP.
import { setTransport } from "../debugger/src/api";
import { App } from "../debugger/src/app";
import type { Files } from "./hevm";
import type { DebugRequest, DebugResponse } from "./debug-worker";

/** What the site posts to the page to start a session */
export interface DebugSession {
  kind: "hevm-debug";
  files: Files;
  args: string[];
}

type Body = DebugRequest extends infer R ? (R extends { id: number } ? Omit<R, "id"> : never) : never;

function embedded() {
  const worker = new Worker(new URL("./debug-worker.ts", import.meta.url), { type: "module" });
  let nextId = 0;
  const pending = new Map<number, (r: DebugResponse) => void>();
  worker.onmessage = (e: MessageEvent<DebugResponse>) => {
    pending.get(e.data.id)?.(e.data);
    pending.delete(e.data.id);
  };
  const call = (body: Body) =>
    new Promise<DebugResponse>((resolve) => {
      const id = nextId++;
      pending.set(id, resolve);
      worker.postMessage({ id, ...body } as DebugRequest);
    });

  setTransport(async (method, path, body) => {
    const r = await call({ kind: "api", method, path, ...(body !== undefined && { body }) });
    if (!r.ok) throw new Error(r.error);
    return { status: r.status, text: r.text };
  });

  const status = document.getElementById("status")!;
  window.addEventListener("message", async (e: MessageEvent<DebugSession>) => {
    if (e.source !== window.parent || e.data?.kind !== "hevm-debug") return;
    status.textContent = "Starting hevm…";
    const r = await call({
      kind: "start",
      wasmUrl: new URL("../hevm-web.wasm", document.baseURI).href,
      glueUrl: new URL("../hevm-web.js", document.baseURI).href,
      files: e.data.files,
      args: e.data.args,
    });
    if (!r.ok) {
      status.textContent = "";
      const pre = document.createElement("pre");
      pre.className = "start-error";
      pre.textContent = r.error;
      status.append(pre);
      return;
    }
    void new App().start();
  });
  window.parent.postMessage({ kind: "hevm-debugger-ready" }, "*");
}

if (window.parent !== window) embedded();
else void new App().start();
