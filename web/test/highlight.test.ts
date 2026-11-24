import { describe, expect, it } from "vitest";
import { segments, tokens } from "../src/highlight";

describe("highlight", () => {
  const src = "contract A {\n  /* a\n  b */ uint256 x = 0x10; // c\n}";

  it("finds tokens like the editor, across lines", () => {
    const t = tokens(src).map((t) => [src.slice(t.from, t.to), t.cls]);
    expect(t).toContainEqual(["contract", "tok-keyword"]);
    expect(t).toContainEqual(["b */", "tok-comment"]);
    expect(t).toContainEqual(["0x10", "tok-number"]);
    expect(t).toContainEqual(["// c", "tok-comment"]);
  });

  it("cuts a line at tokens and the mark", () => {
    const from = src.indexOf("b */");
    const to = src.indexOf("\n}");
    const mark = src.indexOf("x = 0x10");
    const segs = segments(src, tokens(src), from, to, [mark, mark + "x = 0x10".length]);
    expect(segs.map((s) => s.text).join("")).toBe(src.slice(from, to));
    expect(segs.filter((s) => s.marked).map((s) => s.text).join("")).toBe("x = 0x10");
    expect(segs.find((s) => s.text === "0x10")).toEqual({ text: "0x10", cls: "tok-number", marked: true });
    expect(segs.find((s) => s.text === "uint256")).toEqual({ text: "uint256", cls: "tok-keyword", marked: false });
  });
});
