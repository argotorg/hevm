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


// An opcode and the data it pushes, as hex
export function opcode(op: string, arg: string | null): Piece[] {
  return arg === null ? [{ text: op, kind: "opcode" }] : [{ text: op, kind: "opcode" }, { text: " ", kind: null }, ...number(arg)];
}

// Bytes, given as hex, as hex dump rows: offset, sixteen bytes in groups of four, then as text
export function memoryRows(hex: string): Piece[][] {
  const bytes = hex.replace(/^0x/, "").match(/../g) ?? [];
  const rows: Piece[][] = [];
  for (let off = 0; off < bytes.length; off += 16) {
    const row = bytes.slice(off, off + 16);
    const out: Piece[] = [{ text: off.toString(16).padStart(4, "0") + ":", kind: "mem-addr" }];
    row.forEach((b, i) => {
      out.push({ text: i % 4 === 0 ? "  " : " ", kind: null }, { text: b, kind: b === "00" ? "mem-zero" : "mem-byte" });
    });
    const ascii = row.map((b) => {
      const c = parseInt(b, 16);
      return c >= 0x20 && c < 0x7f ? String.fromCharCode(c) : ".";
    });
    out.push({ text: "   " + "   ".repeat(16 - row.length), kind: null }, { text: ascii.join(""), kind: "mem-ascii" });
    rows.push(out);
  }
  return rows;
}

// How a run ended, in words
export function resultText(r: { outcome: string; output: { hex: string } | { expr: string } | null; problem: string | null }): string {
  const output = r.output === null ? "" : "hex" in r.output ? (r.output.hex === "0x" ? ", returned nothing" : `, returned ${r.output.hex}`) : ", returned a symbolic value";
  return r.outcome + output + (r.problem === null ? "" : `: ${r.problem}`);
}
