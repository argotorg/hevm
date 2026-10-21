import assert from "node:assert/strict";
import { describe, test } from "node:test";
import { expr, memoryLine, number, opcode, solidityLines, stackWord, unwrap, word, type Piece } from "../src/highlight";

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
    assert.deepEqual(kinds(opcode("ADD")), ["opcode"]);
    assert.deepEqual(opcode("PUSH2 0x0100").map((p) => p.text), ["PUSH2", " ", "0x0100", "256"]);
  });
  test("stack words as the server shows them", () => {
    assert.deepEqual(stackWord("0x69 (105)"), number("0x69"));
    assert.equal(kindOf(stackWord("(Max\n  100\n  (BufLength\n    (AbstractBuf \"txdata\")\n  )\n)"), "Max"), "expr-ctor");
  });
  test("words sent as JSON", () => {
    assert.deepEqual(word({ hex: "0x20" }), number("0x20"));
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
  const line = "0010:   00 41 00 00  00 00 00 00  00 00 00 00  00 00 00 00   .A..............";
  test("a dump line keeps its text", () => assert.equal(joined(memoryLine(line)), line));
  test("offset, zero and other bytes, and the text column", () => {
    const out = memoryLine(line);
    assert.equal(out[0]?.kind, "mem-addr");
    assert.equal(kindOf(out, "41"), "mem-byte");
    assert.equal(kindOf(out, "00"), "mem-zero");
    assert.equal(out[out.length - 1]?.kind, "mem-ascii");
  });
  test("the header, and symbolic memory", () => {
    assert.deepEqual(kinds(memoryLine("Length: 32 (0x20) bytes")), ["mem-header"]);
    assert.equal(kindOf(memoryLine("(WriteWord"), "WriteWord"), "expr-ctor");
  });
});
