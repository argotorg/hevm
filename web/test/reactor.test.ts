// The debugger on hevm-web.wasm, the reactor build, as the website's debugger tab drives it.
import { existsSync, readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import { beforeAll, describe, expect, it } from "vitest";
import { Reactor, type JsffiGlue } from "../src/reactor";
import { compileProject, type Soljson } from "../src/solc";
import { solExamples } from "../src/solExamples";

const dist = fileURLToPath(new URL("../../dist-wasm/", import.meta.url));
const solc = createRequire(import.meta.url)("solc/soljson.js") as Soljson;
let module: WebAssembly.Module;
let glue: JsffiGlue;

beforeAll(async () => {
  if (!existsSync(`${dist}hevm-web.wasm`)) throw new Error("dist-wasm/hevm-web.wasm is missing: run wasm/build.sh first");
  module = await WebAssembly.compile(readFileSync(`${dist}hevm-web.wasm`));
  glue = ((await import(/* @vite-ignore */ `${dist}hevm-web.js`)) as { default: JsffiGlue }).default;
});

async function session(test: string, calldata?: string) {
  const source = solExamples.find((e) => e.name === "Find x, prove a bound")!.source;
  const project = compileProject(solc, [{ path: "src/Main.sol", content: source }]);
  const reactor = await Reactor.start(module, glue, { files: project.files });
  const exited = reactor.main([
    "test", "--root", "/", "--match", `^${test}$`, "--interactive", ...(calldata ? ["--calldata", calldata] : []),
  ]);
  // the session's routes appear once hevm has set the test up
  let state = await reactor.api("GET", "/state");
  for (let i = 0; state.status === 404 && i < 200; i++) {
    await new Promise((r) => setTimeout(r, 25));
    state = await reactor.api("GET", "/state");
  }
  return { reactor, exited, state };
}

describe("the debugger on the reactor", () => {
  it("serves a session, steps it, and quits", async () => {
    const { reactor, exited, state } = await session("prove_linear");
    expect(state.status).toBe(200);
    expect(state.contentType).toBe("application/json");
    const view = JSON.parse(state.content);
    expect(view).toHaveProperty("step");

    const stepped = await reactor.api("POST", "/command", JSON.stringify({ command: "step 5" }));
    expect(stepped.status).toBe(200);
    expect(JSON.parse(stepped.content).step).toBeGreaterThan(view.step);

    for (const path of ["/stats", "/progress", "/help", "/trace"]) {
      const r = await reactor.api("GET", path);
      expect(r.status, path).toBe(200);
      JSON.parse(r.content);
    }
    expect((await reactor.api("GET", "/nope")).status).toBe(404);

    expect((await reactor.api("POST", "/quit")).status).toBe(200);
    expect(await exited).toBe(0);
  });

  it("replays a counterexample to its failure", async () => {
    const cex = "0x82d4ea10" + "1f".padStart(64, "0");
    const { reactor, exited } = await session("prove_linear", cex);
    // straight to the failure: with concrete calldata there is no branch to pick
    const done = JSON.parse((await reactor.api("POST", "/command", JSON.stringify({ command: "continue" }))).content);
    expect(done.status).toBe("halted");
    expect(done.result.outcome).not.toBe("success");
    await reactor.api("POST", "/quit");
    expect(await exited).toBe(0);
  });

  it("explores the same test symbolically", async () => {
    const { reactor, exited } = await session("prove_linear");
    const stopped = JSON.parse((await reactor.api("POST", "/command", JSON.stringify({ command: "continue" }))).content);
    expect(stopped.status).not.toBe("halted");
    expect(stopped.branch).not.toBeNull();
    await reactor.api("POST", "/quit");
    expect(await exited).toBe(0);
  });
});
