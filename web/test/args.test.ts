import { describe, expect, it } from "vitest";
import { buildArgs, normaliseHex, parseOutcome, stripAnsi } from "../src/hevm";

describe("normaliseHex", () => {
  it("adds 0x, drops whitespace and lowercases", () => {
    expect(normaliseHex(" 60 2A\n f3 ", "code")).toBe("0x602af3");
    expect(normaliseHex("0XFF", "code")).toBe("0xff");
    expect(normaliseHex("", "calldata")).toBe("0x");
  });

  it("rejects odd lengths and non-hex", () => {
    expect(() => normaliseHex("0x6", "code")).toThrow(/code must be hex bytes/);
    expect(() => normaliseHex("0xzz", "code")).toThrow();
  });
});

describe("buildArgs", () => {
  it("passes calldata only to exec", () => {
    expect(buildArgs({ mode: "exec", code: "00", calldata: "01" })).toEqual([
      "exec", "--code", "0x00", "--calldata", "0x01",
    ]);
    expect(buildArgs({ mode: "symbolic", code: "00", calldata: "01" })).toEqual([
      "symbolic", "--code", "0x00",
    ]);
  });

  it("passes a signature only to symbolic", () => {
    expect(buildArgs({ mode: "symbolic", code: "00", sig: " f(uint256) " })).toEqual([
      "symbolic", "--code", "0x00", "--sig", "f(uint256)",
    ]);
    expect(buildArgs({ mode: "exec", code: "00", sig: "f(uint256)" })).toEqual(["exec", "--code", "0x00"]);
  });
});

describe("parseOutcome", () => {
  const run = (stdout: string, stderr = "", exitCode = 0) => ({ stdout, stderr, exitCode });

  it("reads exec results", () => {
    expect(parseOutcome("exec", run('"Return: 0xabcd"'))).toEqual({ kind: "return", data: "0xabcd" });
    expect(parseOutcome("exec", run("Revert: 0x"))).toEqual({ kind: "revert", data: "0x" });
  });

  it("reads counterexamples past the colour codes", () => {
    const out = [
      "Using assertion code(s): 1",
      "",
      "Discovered the following 1 counterexample(s):",
      "",
      "\x1b[1mCalldata:\x1b[0m",
      "  0x000000000000000000000000000000000000000000000000000000000000002a",
      "\x1b[1mStorage:\x1b[0m",
    ].join("\n");
    expect(parseOutcome("symbolic", run(out))).toEqual({
      kind: "counterexamples",
      calldata: ["0x000000000000000000000000000000000000000000000000000000000000002a"],
    });
  });

  it("reads a proof", () => {
    expect(parseOutcome("symbolic", run("QED: No reachable property violations discovered"))).toEqual({
      kind: "safe",
    });
  });

  it("reports anything else as an error, with stderr first", () => {
    expect(parseOutcome("exec", run("", "Error: boom", 1))).toEqual({ kind: "error", message: "Error: boom" });
    expect(parseOutcome("symbolic", run("", "", 3))).toEqual({
      kind: "error",
      message: "hevm exited with code 3",
    });
  });
});

describe("stripAnsi", () => {
  it("removes SGR sequences", () => {
    expect(stripAnsi("\x1b[1mbold\x1b[0m \x1b[31;1mred\x1b[0m")).toBe("bold red");
  });
});
