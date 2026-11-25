// The debugger's page. Opened by the site, in a window of its own, it debugs the session the
// site hands it on hevm-web.wasm, in a worker; opened by itself it talks to a running
// `hevm ... --interactive` over HTTP.
import { setTransport } from "../debugger/src/api";
import { App } from "../debugger/src/app";
import type { Files } from "./hevm";
import type { DebugRequest, DebugResponse } from "./debug-worker";

/** What the site hands a debugger window, which asks for it by its id */
export interface DebugSession {
  kind: "hevm-debug";
  id: string;
  files: Files;
  args: string[];
  /** the window's title, and what the session is about */
  title: string;
  caption: string;
}

type Body = DebugRequest extends infer R ? (R extends { id: number } ? Omit<R, "id"> : never) : never;

function fromSite(site: Window, sessionId: string) {
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
  const caption = document.getElementById("session")!;
  const showError = (text: string) => {
    const pre = document.createElement("pre");
    pre.className = "start-error";
    pre.textContent = text;
    status.replaceChildren(pre);
  };
  let started = false;
  window.addEventListener("message", async (e: MessageEvent<DebugSession>) => {
    if (started || e.source !== site || e.origin !== location.origin) return;
    if (e.data?.kind !== "hevm-debug" || e.data.id !== sessionId) return;
    started = true;
    document.title = e.data.title;
    caption.textContent = e.data.caption;
    caption.hidden = false;
    status.textContent = "Starting hevm…";
    const r = await call({
      kind: "start",
      wasmUrl: new URL("../hevm-web.wasm", document.baseURI).href,
      glueUrl: new URL("../hevm-web.js", document.baseURI).href,
      files: e.data.files,
      args: e.data.args,
    });
    if (!r.ok) return showError(r.error);
    void new App().start();
  });
  // the site keeps the session while it is open: a reloaded window gets it again
  setTimeout(() => {
    if (!started) showError("The page this session came from is closed, or has gone elsewhere: start it again from its results.");
  }, 3000);
  if (!site.closed) site.postMessage({ kind: "hevm-debugger-ready", id: sessionId }, location.origin);
}

const sessionId = new URLSearchParams(location.search).get("session");
if (window.opener && sessionId) fromSite(window.opener as Window, sessionId);
else void new App().start();
