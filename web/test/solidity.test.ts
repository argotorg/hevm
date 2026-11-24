// Compiles with soljson and proves with hevm.wasm, as the website does.
import { existsSync, readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import { beforeAll, describe, expect, it } from "vitest";
import { runHevm } from "../src/hevm";
import { describeResult, parseTestOutput } from "../src/results";
import { compileProject, solcVersion, type Soljson } from "../src/solc";
import { solExamples } from "../src/solExamples";

const wasmPath = fileURLToPath(new URL("../../dist-wasm/hevm.wasm", import.meta.url));
const solc = createRequire(import.meta.url)("solc/soljson.js") as Soljson;
let module: WebAssembly.Module;

beforeAll(async () => {
  if (!existsSync(wasmPath)) throw new Error(`${wasmPath} is missing: run wasm/build.sh first`);
  module = await WebAssembly.compile(readFileSync(wasmPath));
});

const example = (name: string) => solExamples.find((e) => e.name === name)!.source;

async function prove(source: string) {
  const project = compileProject(solc, [{ path: "src/Main.sol", content: source }]);
  expect(project.errors.filter((e) => e.severity === "error")).toEqual([]);
  const run = await runHevm(module, ["test", "--root", "/"], project.files);
  return Object.fromEntries(parseTestOutput(run.stdout).map((r) => [r.name, r]));
}

describe("soljson", () => {
  it("is the pinned version", () => {
    expect(solcVersion(solc)).toMatch(/^0\.8\.39\+/);
  });

  it("reports compile errors with their location", () => {
    const content = "pragma solidity ^0.8.0;\ncontract C { function f() public { x = 1; } }\n";
    const project = compileProject(solc, [{ path: "src/Main.sol", content }]);
    const error = project.errors.find((e) => e.severity === "error")!;
    expect(error.message).toMatch(/Undeclared identifier/);
    expect(error.file).toBe("src/Main.sol");
    expect(error.start).toBe(content.indexOf("x = 1"));
  });
});

describe("hevm test on soljson output", () => {
  it("finds counterexamples and where they fail", async () => {
    const res = await prove(example("Assertions"));
    expect(res["prove_fits(uint8,uint8)"]).toMatchObject({ status: "pass", counterexamples: [] });
    const linear = res["prove_linear(uint256)"]!;
    expect(linear.status).toBe("fail");
    expect(linear.counterexamples).toEqual([
      {
        validated: true,
        calldata: "prove_linear(31)",
        result: "Revert: 0x4e487b71" + "0".repeat(63) + "1",
        at: { file: "src/Main.sol", line: 10, column: 13, code: "assert(x * 3 + 7 != 100)" },
      },
    ]);
    expect(describeResult(linear.counterexamples[0]!.result)).toBe("Panic(0x01): assertion failed");
  });

  it("finds the self-transfer bug", async () => {
    const t = (await prove(example("Token with a bug")))["prove_transfer(address,uint256)"]!;
    expect(t.status).toBe("fail");
    expect(t.counterexamples[0]!.at).toMatchObject({
      line: 29,
      code: "assert(token.balanceOf(address(this)) + token.balanceOf(to) == before)",
    });
  });

  it("locates a failure in a called contract there", async () => {
    const t = (await prove(example("Failure in a called contract")))["prove_deposit(uint256)"]!;
    expect(t.counterexamples[0]!.at).toMatchObject({ line: 11, code: "assert(total < 1000)" });
  });
});
