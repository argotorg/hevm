// hevm-web.wasm: hevm as a WASI reactor, which stays alive between calls, for the debugger.
import type { WASI } from "@bjorn3/browser_wasi_shim";
import { hevmWasi, type RunOptions } from "./hevm";

/** The default export of hevm-web.js, which GHC's post-linker writes: the JSFFI imports */
export type JsffiGlue = (exports: Record<string, unknown>) => WebAssembly.ModuleImports;

export interface ApiResponse {
  status: number;
  contentType: string;
  content: string;
}

interface Exports {
  hevm_main(argsJson: string): Promise<number>;
  hevm_api(method: string, path: string, body: string): Promise<string>;
}

export class Reactor {
  private constructor(
    private readonly exports: Exports,
    readonly stdout: string[],
    readonly stderr: string[],
  ) {}

  static async start(module: WebAssembly.Module, glue: JsffiGlue, opts: RunOptions = {}): Promise<Reactor> {
    const { wasi, stdout, stderr } = hevmWasi([], opts);
    const exports: Record<string, unknown> = {};
    const instance = await WebAssembly.instantiate(module, {
      wasi_snapshot_preview1: wasi.wasiImport,
      ghc_wasm_jsffi: glue(exports),
    });
    Object.assign(exports, instance.exports);
    wasi.initialize(instance as unknown as Parameters<WASI["initialize"]>[0]);
    return new Reactor(exports as unknown as Exports, stdout, stderr);
  }

  /** hevm's main with these arguments; with --interactive it runs until the debugger quits */
  main(args: string[]): Promise<number> {
    return this.exports.hevm_main(JSON.stringify(args));
  }

  /** A request to the debugger's API, answered as its HTTP server would */
  async api(method: string, path: string, body = ""): Promise<ApiResponse> {
    return JSON.parse(await this.exports.hevm_api(method, path, body)) as ApiResponse;
  }
}
