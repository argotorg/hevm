// Checks equivalence of Solidity with hevm.wasm, as the website's Equivalence tab does.
import { existsSync, readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import { beforeAll, describe, expect, it } from "vitest";
import { describeCall, describeOutcome, decodeWord, signature } from "../src/abi";
import { eqExamples } from "../src/eqExamples";
import { parseEquivalence } from "../src/eqOutput";
import { contractNames, eqArgs, eqPrograms } from "../src/equivalence";
import { runHevm } from "../src/hevm";
import { compileProject, type Soljson } from "../src/solc";

const wasmPath = fileURLToPath(new URL("../../dist-wasm/hevm.wasm", import.meta.url));
const solc = createRequire(import.meta.url)("solc/soljson.js") as Soljson;
let module: WebAssembly.Module;

beforeAll(async () => {
  if (!existsSync(wasmPath)) throw new Error(`${wasmPath} is missing: run wasm/build.sh first`);
  module = await WebAssembly.compile(readFileSync(wasmPath));
});

async function check(name: string) {
  const ex = eqExamples.find((e) => e.name === name)!;
  const prepared = await eqPrograms((s, st) => compileProject(solc, s, st), ex.source, ex.mode, ex.a, ex.b);
  if ("errors" in prepared) throw new Error(prepared.errors.map((e) => e.formatted).join("\n"));
  const [a, b] = prepared.programs;
  const run = await runHevm(module, eqArgs(a, b).slice(0, 5));
  const result = parseEquivalence(run.stdout);
  const fn = a.abi[0]!;
  const cexes = result.counterexamples.map((c) => ({
    call: describeCall(c.calldata, a.abi, a.selectors),
    a: describeOutcome(c.a ?? "", a.abi.find((f) => signature(f) === signature(fn))?.outputs),
    b: describeOutcome(c.b ?? "", b.abi[0]?.outputs),
    validated: c.validated,
  }));
  return { verdict: result.verdict, cexes, warnings: result.warnings, a, b };
}

describe("equivalence examples", () => {
  it("proves the branch-free min and max", async () => {
    expect((await check("Branch-free min and max")).verdict).toBe("equivalent");
  });

  it("finds where the cheaper average differs", async () => {
    const r = await check("A cheaper average");
    expect(r.verdict).toBe("different");
    expect(r.cexes[0]).toMatchObject({ a: "reverts: Panic(0x11): arithmetic overflow or underflow", validated: true });
    expect(r.cexes[0]!.call).toMatch(/^average\(0x[0-9a-f]+, 0x[0-9a-f]+\)$/);
    expect(r.cexes[0]!.b).toMatch(/^returns 0x[0-9a-f]+$/);
  });

  it("finds the zero case", async () => {
    const r = await check("Forgot the zero case");
    expect(r.verdict).toBe("different");
    expect(r.cexes[0]).toEqual({ call: "isPowerOfTwo(0)", a: "returns false", b: "returns true", validated: true });
  });

  it("finds an empty range", async () => {
    const r = await check("One comparison instead of two");
    expect(r.verdict).toBe("different");
    const [, lo, hi] = /^inRange\((?:0x)?[0-9a-f]+, ((?:0x)?[0-9a-f]+), ((?:0x)?[0-9a-f]+)\)$/.exec(r.cexes[0]!.call)!;
    expect(BigInt(lo!)).toBeGreaterThan(BigInt(hi!));
  });

  it("proves the optimizer changes nothing", async () => {
    const r = await check("Does the optimizer change anything?");
    expect(r.a.code).not.toBe(r.b.code);
    expect(r.verdict).toBe("equivalent");
  });

  it("proves via-IR changes nothing", async () => {
    const r = await check("Legacy codegen vs via-IR");
    expect(r.a.code).not.toBe(r.b.code);
    expect(r.verdict).toBe("equivalent");
  });
});

describe("contract names", () => {
  it("are read from the source", () => {
    expect(contractNames("contract A {}\n// contract C {}\n/* contract D {} */\n  contract B is A {}")).toEqual(["A", "B"]);
    for (const ex of eqExamples) expect(contractNames(ex.source)).toContain(ex.a);
  });
});

const word = (n: bigint) => (n < 0n ? n + (1n << 256n) : n).toString(16).padStart(64, "0");

describe("abi", () => {

  it("decodes words", () => {
    expect(decodeWord("uint256", word(1337n))).toBe("1337");
    expect(decodeWord("int8", word(-5n))).toBe("-5");
    expect(decodeWord("uint256", word(1n << 255n))).toBe("0x8" + "0".repeat(63));
    expect(decodeWord("int256", word(-(1n << 100n)))).toBe("-0x1" + "0".repeat(25));
    expect(decodeWord("bool", word(1n))).toBe("true");
    expect(decodeWord("bool", word(2n))).toBeUndefined();
    expect(decodeWord("address", word(0xabcn))).toBe("0x" + "0".repeat(37) + "abc");
    expect(decodeWord("bytes2", "beef" + "0".repeat(60))).toBe("0xbeef");
    expect(decodeWord("string", word(0n))).toBeUndefined();
  });

  it("describes calls and outcomes", () => {
    const f = { type: "function" as const, name: "f", inputs: [{ name: "x", type: "uint8" }], outputs: [{ name: "", type: "bool" }] };
    expect(signature(f)).toBe("f(uint8)");
    expect(describeCall("0x12345678" + word(7n), [f], { "f(uint8)": "12345678" })).toBe("f(7)");
    expect(describeCall("0xdeadbeef", [f], { "f(uint8)": "12345678" })).toBe("0xdeadbeef");
    expect(describeOutcome("Return 0x" + word(1n), f.outputs)).toBe("returns true");
    expect(describeOutcome("Return 0x", [])).toBe("returns nothing");
    expect(describeOutcome("Return 0x" + word(5n) + ", storage 0=1", undefined)).toBe("returns 0x" + word(5n) + " (storage 0=1)");
    expect(describeOutcome("Revert 0x4e487b71" + word(0x12n) + " = Panic(18)")).toBe("reverts: Panic(0x12): division or modulo by zero");
    expect(describeOutcome("BadJumpDestination")).toBe("fails: BadJumpDestination");
  });
});

describe("equivalence output", () => {
  it("is parsed", () => {
    const out = [
      "   \x1b[31m[FAIL]\x1b[0m Contracts do not behave equivalently",
      "   \x1b[33m[WARNING]\x1b[0m hevm was only able to partially explore the contracts under test due to: ",
      "      2x -> Max Iterations Reached",
      "",
      "Not equivalent. This input results in differing behaviours:",
      "-----",
      "\x1b[1mCalldata:\x1b[0m",
      "  0xb3de648b" + word(1337n),
      "\x1b[1mDifference:\x1b[0m Deployed contracts. Success vs Failure end states",
      "A ret: (WriteWord",
      "  A: not this",
      "B err: BadJumpDestination",
      "\x1b[1mConcrete replay:\x1b[0m \x1b[90m[validated]\x1b[0m",
      "  A: Return 0x" + word(2674n),
      "  B: BadJumpDestination",
    ].join("\n");
    expect(parseEquivalence(out)).toEqual({
      verdict: "different",
      warnings: ["2x -> Max Iterations Reached"],
      counterexamples: [{
        calldata: "0xb3de648b" + word(1337n),
        difference: "Deployed contracts. Success vs Failure end states",
        validated: true,
        a: "Return 0x" + word(2674n),
        b: "BadJumpDestination",
      }],
    });
    expect(parseEquivalence("   [PASS] Contracts behave equivalently\nNo discrepancies found\n").verdict).toBe("equivalent");
  });
});
