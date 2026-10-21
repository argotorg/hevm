// Splitting text into classed pieces for the panes to colour. Pure: the colours are in the CSS.
import Prism, { type TokenStream } from "./vendor/prism.js";

// A piece of text and its kind, which the view turns into a class; null is plain text
export interface Piece {
  text: string;
  kind: string | null;
}

function flatten(stream: TokenStream, kind: string | null, out: Piece[]): void {
  if (typeof stream === "string") out.push({ text: stream, kind });
  else if (Array.isArray(stream)) for (const s of stream) flatten(s, kind, out);
  else flatten(stream.content, `tok-${stream.type}`, out);
}

// Solidity lines, tokenized together so that a comment or string may span lines
export function solidityLines(lines: string[]): Piece[][] {
  const pieces: Piece[] = [];
  flatten(Prism.tokenize(lines.join("\n"), Prism.languages["solidity"]), null, pieces);
  const result: Piece[][] = [[]];
  for (const p of pieces) {
    p.text.split("\n").forEach((part, i) => {
      if (i > 0) result.push([]);
      if (part !== "") result[result.length - 1]!.push({ text: part, kind: p.kind });
    });
  }
  return result;
}

const hexWord = /^0x[0-9a-f]+$/i;

// A word as hex, and as decimal when that helps: small enough to read, too big to be the same digit
export function number(hex: string): Piece[] {
  if (!hexWord.test(hex)) return [{ text: hex, kind: null }];
  const v = BigInt(hex);
  return v > 9n && v < 0x10000n ? [{ text: hex, kind: "num-hex" }, { text: v.toString(), kind: "num-dec" }] : [{ text: hex, kind: "num-hex" }];
}

const exprToken = /("(?:[^"\\]|\\.)*")|(\b0x[0-9a-fA-F]+\b)|(\b\d+\b)|([A-Za-z_]\w*:)|(\b[A-Z]\w*)|([()])/g;
const exprKinds = ["expr-str", "num-hex", "expr-num", "expr-field", "expr-ctor", "expr-paren"];

// One of hevm's symbolic expressions, like "(Max 100 (BufLength (AbstractBuf "txdata")))"
export function expr(text: string): Piece[] {
  const out: Piece[] = [];
  let last = 0;
  for (const m of text.matchAll(exprToken)) {
    if (m.index > last) out.push({ text: text.slice(last, m.index), kind: null });
    const group = m.slice(1).findIndex((g) => g !== undefined);
    out.push({ text: m[0], kind: exprKinds[group] ?? null });
    last = m.index + m[0].length;
  }
  if (last < text.length) out.push({ text: text.slice(last), kind: null });
  return out;
}

// An expression without the brackets around all of it, which are only noise on screen
export function unwrap(text: string): string {
  if (!text.startsWith("(") || !text.endsWith(")")) return text;
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    if (text[i] === "(") depth++;
    else if (text[i] === ")") depth--;
    if (depth === 0 && i < text.length - 1) return text;
  }
  return text.slice(1, -1).trimEnd();
}

// An expression as the panes show it
export function shownExpr(text: string): Piece[] {
  return expr(unwrap(text));
}

// A word the server sends as JSON
export function word(w: { hex: string } | { expr: string }): Piece[] {
  return "hex" in w ? number(w.hex) : shownExpr(w.expr);
}

// A word as the server shows it: "0x69 (105)", a bare hex word, or an expression
export function stackWord(text: string): Piece[] {
  const m = /^(0x[0-9a-f]+)(?: \(\d+\))?$/i.exec(text);
  return m?.[1] !== undefined ? number(m[1]) : shownExpr(text);
}

// An opcode and its argument, like "PUSH2 0x0100"
export function opcode(text: string): Piece[] {
  const space = text.indexOf(" ");
  if (space < 0) return [{ text, kind: "opcode" }];
  return [{ text: text.slice(0, space), kind: "opcode" }, { text: " ", kind: null }, ...number(text.slice(space + 1))];
}

// One line of the server's hex dump: offset, bytes, then the bytes as text
export function memoryLine(line: string): Piece[] {
  const m = /^([0-9a-f]+:)( +)(.*)$/i.exec(line);
  if (m === null) return /^Length:/.test(line) ? [{ text: line, kind: "mem-header" }] : expr(line);
  const [, addr = "", gap = "", rest = ""] = m;
  // byte groups are at most two spaces apart, the text column three
  const split = rest.search(/ {3,}/);
  const bytes = split < 0 ? rest : rest.slice(0, split);
  const out: Piece[] = [{ text: addr, kind: "mem-addr" }, { text: gap, kind: null }];
  for (const part of bytes.split(/( +)/)) {
    if (part === "") continue;
    out.push({ text: part, kind: part.trim() === "" ? null : part === "00" ? "mem-zero" : "mem-byte" });
  }
  if (split >= 0) {
    const text = rest.slice(split);
    const lead = text.length - text.trimStart().length;
    out.push({ text: text.slice(0, lead), kind: null }, { text: text.slice(lead), kind: "mem-ascii" });
  }
  return out;
}
