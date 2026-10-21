import assert from "node:assert/strict";
import { describe, test } from "node:test";
import { expr, memoryRows, number, opcode, resultText, solidityLines, unwrap, word, type Piece } from "../src/highlight";

const joined = (ps: Piece[]): string => ps.map((p) => p.text).join("");
const kinds = (ps: Piece[]): (string | null)[] => ps.map((p) => p.kind);
const kindOf = (ps: Piece[], text: string): string | null | undefined => ps.find((p) => p.text === text)?.kind;

describe("solidity", () => {
  const lines = ["function f(uint8 x) public returns (uint256) {", "  /* a", "  b */ return 0x10;", "}"];
  const out = solidityLines(lines);

  test("keeps every line, and its text", () => {
    assert.equal(out.length, lines.length);
    out.forEach((ps, i) => assert.equal(joined(ps), lines[i]));
  });
  test("classes keywords, types and numbers", () => {
    assert.equal(kindOf(out[0]!, "function"), "tok-keyword");
    assert.equal(kindOf(out[0]!, "uint8"), "tok-builtin");
    assert.equal(kindOf(out[2]!, "0x10"), "tok-number");
  });
  test("a comment spanning lines stays a comment", () => {
    assert.equal(out[1]![1]?.kind, "tok-comment");
    assert.equal(out[2]![0]?.kind, "tok-comment");
    assert.equal(kindOf(out[2]!, "return"), "tok-keyword");
  });
});

describe("numbers", () => {
  test("small words also in decimal", () => {
    assert.deepEqual(number("0x10"), [{ text: "0x10", kind: "num-hex" }, { text: "16", kind: "num-dec" }]);
    assert.deepEqual(kinds(number("0x5")), ["num-hex"]);
    assert.deepEqual(kinds(number("0x10000")), ["num-hex"]);
    assert.deepEqual(kinds(number("0x" + "f".repeat(64))), ["num-hex"]);
  });
  test("opcodes and their arguments", () => {
    assert.deepEqual(kinds(opcode("ADD", null)), ["opcode"]);
    assert.deepEqual(opcode("PUSH2", "0x0100").map((p) => p.text), ["PUSH2", " ", "0x0100", "256"]);
  });
  test("words sent as JSON", () => {
    assert.deepEqual(word({ hex: "0x20" }), number("0x20"));
    assert.equal(kindOf(word({ expr: "(Max\n  100\n  (BufLength\n    (AbstractBuf \"txdata\")\n  )\n)" }), "Max"), "expr-ctor");
    assert.equal(joined(word({ expr: "(Keccak (ConcreteBuf \"\"))" })), "Keccak (ConcreteBuf \"\")");
  });
});

describe("expressions", () => {
  const e = '(Max\n  100\n  (BufLength\n    buf:\n      (AbstractBuf "txdata")\n  )\n)';
  const out = expr(e);
  test("keep their text", () => assert.equal(joined(out), e));
  test("class constructors, fields, numbers, strings and brackets", () => {
    assert.equal(kindOf(out, "Max"), "expr-ctor");
    assert.equal(kindOf(out, "BufLength"), "expr-ctor");
    assert.equal(kindOf(out, "buf:"), "expr-field");
    assert.equal(kindOf(out, "100"), "expr-num");
    assert.equal(kindOf(out, '"txdata"'), "expr-str");
    assert.equal(kindOf(out, "("), "expr-paren");
  });
});

describe("unwrapping", () => {
  test("drops the brackets around a whole expression, and the newline before the last", () => {
    assert.equal(unwrap("(Max\n  100\n  (BufLength\n    (AbstractBuf \"txdata\")\n  )\n)"), "Max\n  100\n  (BufLength\n    (AbstractBuf \"txdata\")\n  )");
    assert.equal(unwrap("(Caller)"), "Caller");
  });
  test("keeps brackets that do not enclose it all", () => {
    assert.equal(unwrap("(A) (B)"), "(A) (B)");
    assert.equal(unwrap("Caller"), "Caller");
    assert.equal(unwrap("()"), "");
  });
});

describe("memory", () => {
  const rows = memoryRows("0x" + "00".repeat(16) + "0041ff");
  test("sixteen bytes a row, the last one padded", () => {
    assert.equal(rows.length, 2);
    assert.equal(joined(rows[0]!), "0000:  00 00 00 00  00 00 00 00  00 00 00 00  00 00 00 00   ................");
    assert.equal(joined(rows[1]!), "0010:  00 41 ff" + " ".repeat(3 + 13 * 3) + ".A.");
  });
  test("offset, zero and other bytes, and the text column", () => {
    const row = rows[1]!;
    assert.equal(row[0]?.kind, "mem-addr");
    assert.equal(kindOf(row, "41"), "mem-byte");
    assert.equal(kindOf(row, "00"), "mem-zero");
    assert.equal(row[row.length - 1]?.kind, "mem-ascii");
    assert.deepEqual(memoryRows("0x"), []);
  });
});

describe("results", () => {
  test("in words", () => {
    assert.equal(resultText({ outcome: "success", output: { hex: "0x" }, problem: null }), "success, returned nothing");
    assert.equal(resultText({ outcome: "revert", output: { hex: "0x01" }, problem: null }), "revert, returned 0x01");
    assert.equal(resultText({ outcome: "failure", output: null, problem: "BadJumpDestination" }), "failure: BadJumpDestination");
  });
});
