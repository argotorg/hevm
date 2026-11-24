// Compiles with soljson and proves with hevm.wasm, as the website does.
import { existsSync, readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import { beforeAll, describe, expect, it } from "vitest";
import { progressPath, runHevm } from "../src/hevm";
import { newStats, onProgress as progressOnEvent, onStdout as progressOnStdout, testsDone } from "../src/progress";
import { describeResult, parseTestOutput, readableNumbers } from "../src/results";
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
  const run = await runHevm(module, ["test", "--root", "/"], { files: project.files });
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
    const res = await prove(example("Find x, prove a bound"));
    expect(res["prove_fits(uint8,uint8)"]).toMatchObject({ status: "pass", counterexamples: [] });
    const linear = res["prove_linear(uint256)"]!;
    expect(linear.status).toBe("fail");
    expect(linear.counterexamples).toEqual([
      {
        validated: true,
        calldata: "prove_linear(31)",
        raw: "0x82d4ea10" + "1f".padStart(64, "0"),
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

describe("progress of hevm test", () => {
  it("streams events and stdout while it runs", async () => {
    const project = compileProject(solc, [{ path: "src/Main.sol", content: example("Token with a bug") }]);
    const stats = newStats();
    const order: string[] = [];
    await runHevm(module, ["test", "--root", "/", "--progress-log", progressPath], {
      files: project.files,
      onStdout: (l) => {
        order.push("stdout");
        progressOnStdout(stats, l);
      },
      onProgress: (e) => {
        order.push(e.ev);
        progressOnEvent(stats, e);
      },
    });
    expect(stats.total).toBe(1);
    expect(stats.finished).toBe(true);
    expect(testsDone(stats)).toBe(1);
    expect(stats.tests[0]).toMatchObject({ name: "prove_transfer(address,uint256)", cex: 1 });
    expect(stats.paths).toBeGreaterThan(0);
    expect(stats.forks).toBeGreaterThan(0);
    expect(stats.queriesDone).toBeGreaterThan(0);
    expect(stats.queriesInFlight).toBe(0);
    expect(Object.values(stats.results).reduce((a, b) => a + b, 0)).toBe(stats.queriesDone);
    // the events come during the run, between lines of stdout
    expect(order.indexOf("query-end")).toBeLessThan(order.lastIndexOf("stdout"));
  });
});

describe("test output", () => {
  it("has the calls before a failing invariant, and what a pass covered", () => {
    const out = [
      "Checking 2 function(s) in contract src/Main.sol:T",
      "[RUNNING] invariant_a()",
      "   Counterexample:   [validated]",
      "     calls:    Token.mint(18446744073709551616)",
      "               Token.burn(1) from 0x0000000000000000000000000000000000000B0b",
      "     calldata: invariant_a()",
      "     raw:      0x12345678",
      "     result:   Revert: 0x",
      "   [FAIL] invariant_a",
      "[RUNNING] invariant_b()",
      "   [PASS] invariant_b (7 states, up to 2 calls deep)",
    ].join("\n");
    const [a, b] = parseTestOutput(out);
    expect(a!.counterexamples[0]!.calls).toEqual([
      "Token.mint(18446744073709551616)",
      "Token.burn(1) from 0x0000000000000000000000000000000000000B0b",
    ]);
    expect(a!.counterexamples[0]!.calldata).toBe("invariant_a()");
    expect(b).toMatchObject({ status: "pass", detail: "7 states, up to 2 calls deep" });
    expect(readableNumbers("f(18446744073709551615, 18446744073709551616, 0x1)")).toBe("f(18446744073709551615, 0x10000000000000000, 0x1)");
  });
});

// every example on the website, with what hevm must find
type Expectation = { status: "pass" | "fail"; calldata?: string; line?: number; calls?: RegExp[] };
const expectations: Record<string, Record<string, Expectation>> = {
  "Find x, prove a bound": {
    "prove_linear(uint256)": { status: "fail", calldata: "prove_linear(31)", line: 10 },
    "prove_fits(uint8,uint8)": { status: "pass" },
  },
  "Token with a bug": {
    "prove_transfer(address,uint256)": { status: "fail", line: 29 },
  },
  "Failure in a called contract": {
    "prove_deposit(uint256)": { status: "fail", line: 11 },
  },
  "Math library": {
    "prove_min_max(uint256,uint256)": { status: "pass" },
    "prove_ceilDiv(uint256,uint256)": { status: "fail", line: 42 },
    "prove_abs(int256)": {
      status: "fail",
      calldata: "prove_abs(-57896044618658097711785492504343953926634992332820282019728792003956564819968)",
      line: 46,
    },
    "prove_clamp(uint256,uint256,uint256)": { status: "pass" },
    "prove_clamp_keeps(uint256,uint256,uint256)": { status: "pass" },
    "prove_min_commutes(uint256,uint256)": { status: "pass" },
  },
  "Sorting network": {
    "prove_sorted(uint256,uint256,uint256)": { status: "pass" },
    "prove_permutation(uint256,uint256,uint256)": { status: "pass" },
  },
  "Bit tricks": {
    "prove_average(uint128,uint128)": { status: "pass" },
    "prove_powerOfTwo(uint256)": { status: "fail", calldata: "prove_powerOfTwo(0)", line: 24 },
  },
  "Access control": {
    "prove_fee_capped(uint256)": { status: "pass" },
    "prove_only_owner_sets_fee()": { status: "fail", calldata: "prove_only_owner_sets_fee()", line: 44 },
  },
  "Batch transfer overflow (BeautyChain, 2018)": {
    "prove_no_tokens_from_nothing(address,address,uint256)": { status: "fail", line: 33 },
  },
  "Unsafe downcast": {
    "prove_stake_recorded(uint256)": { status: "fail", calldata: "prove_stake_recorded(340282366920938463463374607431768211456)", line: 21 },
  },
  "Share inflation (ERC-4626)": {
    "prove_deposit_gets_shares(uint256,uint256)": { status: "fail", line: 34 },
  },
  "Supply invariant": {
    "invariant_supply()": { status: "fail", line: 37, calls: [/^Token\.mint\(\d+\)$/, /^Token\.burn\(\d+\)$/] },
  },
  "Re-initializable wallet (Parity, 2017)": {
    "invariant_owner()": { status: "fail", line: 32, calls: [/^Wallet\.initWallet\(\) from 0x[0-9a-fA-F]{40}$/] },
  },
  "Escrow state machine": {
    "invariant_one_outcome()": {
      status: "fail",
      line: 45,
      calls: [/^Escrow\.release\(\) from 0x0+b0b$/i, /^Escrow\.refund\(\) from 0x0+5e11e7$/i],
    },
  },
};

describe("the website's examples", () => {
  it("covers every example", () => {
    expect(Object.keys(expectations).sort()).toEqual(solExamples.map((e) => e.name).sort());
  });

  for (const [name, tests] of Object.entries(expectations)) {
    it(name, async () => {
      const res = await prove(example(name));
      expect(Object.keys(res).sort()).toEqual(Object.keys(tests).sort());
      for (const [fn, want] of Object.entries(tests)) {
        const got = res[fn]!;
        expect(got.status, fn).toBe(want.status);
        if (want.status === "pass") {
          expect(got.counterexamples, fn).toEqual([]);
          continue;
        }
        const cex = got.counterexamples[0]!;
        expect(cex.validated, fn).toBe(true);
        if (want.calldata) expect(cex.calldata, fn).toBe(want.calldata);
        expect(cex.at?.line, fn).toBe(want.line);
        if (want.calls) {
          expect(cex.calls?.length, fn).toBe(want.calls.length);
          want.calls.forEach((re, i) => expect(cex.calls![i], fn).toMatch(re));
        } else {
          expect(cex.calls, fn).toBeUndefined();
        }
      }
    });
  }
});
