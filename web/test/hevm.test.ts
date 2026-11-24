// Runs the real hevm.wasm (from wasm/build.sh) through the same WASI shim as the website.
import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { beforeAll, describe, expect, it } from "vitest";
import { buildArgs, parseOutcome, runHevm, type Request } from "../src/hevm";
import { examples } from "../src/examples";

const wasmPath = fileURLToPath(new URL("../../dist-wasm/hevm.wasm", import.meta.url));
let module: WebAssembly.Module;

beforeAll(async () => {
  if (!existsSync(wasmPath)) throw new Error(`${wasmPath} is missing: run wasm/build.sh first`);
  module = await WebAssembly.compile(readFileSync(wasmPath));
});

const hevm = async (req: Request) => parseOutcome(req.mode, await runHevm(module, buildArgs(req)));
const example = (name: string) => examples.find((e) => e.name === name)!.request;

describe("hevm exec", () => {
  it("hashes with keccak", async () => {
    expect(await hevm(example("Keccak of 32 zero bytes"))).toEqual({
      kind: "return",
      data: "0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
    });
  });

  it("does 256-bit arithmetic on a 32-bit target", async () => {
    // 3^200 mod 2^256, and -7 sdiv 2
    expect(await hevm({ mode: "exec", code: "0x60c860030a60005260206000f3" })).toEqual({
      kind: "return",
      data: "0xc21a937a76f3432ffd73d97e447606b683ecf6f6e4a7ae225bfaff1eaaf8b0a1",
    });
    const sdiv = "0x60027f" + "ff".repeat(31) + "f90560005260206000f3";
    expect(await hevm({ mode: "exec", code: sdiv })).toEqual({
      kind: "return",
      data: "0x" + "ff".repeat(31) + "fd",
    });
  });

  it("runs the SHA256 and ecrecover precompiles", async () => {
    expect(await hevm({ mode: "exec", code: "0x602060006000600060025afa5060206000f3" })).toEqual({
      kind: "return",
      data: "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    });
    expect(await hevm(example("ecrecover precompile"))).toEqual({
      kind: "return",
      data: "0x0000000000000000000000002d5e56d45c63150d937f2182538a0f18510cb11f",
    });
  });

  it("reports a revert", async () => {
    expect(await hevm(example("Revert"))).toEqual({ kind: "revert", data: "0x" });
  });

  it("reports BN254 precompiles as unsupported", async () => {
    const res = await hevm({ mode: "exec", code: "0x604060006080600060065afa5060206000f3" });
    expect(res).toMatchObject({ kind: "error" });
    expect(res.kind === "error" && res.message).toMatch(/NonexistentPrecompile/);
  });
});

describe("hevm symbolic with the built-in bitwuzla", () => {
  it("finds the failing input", async () => {
    expect(await hevm(example("Find the input that fails an assertion"))).toEqual({
      kind: "counterexamples",
      calldata: ["0x000000000000000000000000000000000000000000000000000000000000002a"],
    });
  });

  it("solves modular arithmetic", async () => {
    expect(await hevm(example("Solve 3x + 7 = 100 (mod 2^256)"))).toEqual({
      kind: "counterexamples",
      calldata: ["0x000000000000000000000000000000000000000000000000000000000000001f"],
    });
  });

  it("proves a contract without failures", async () => {
    expect(await hevm(example("Prove no input fails"))).toEqual({ kind: "safe" });
  });

  it("refuses solvers it does not have", async () => {
    const res = await runHevm(module, ["symbolic", "--code", "0x00", "--solver", "z3"]);
    expect(res.exitCode).not.toBe(0);
    expect(res.stdout).toMatch(/has bitwuzla built in, and cannot start z3/);
  });
});
