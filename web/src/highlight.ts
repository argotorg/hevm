// Solidity highlighting outside the editor, with the editor's grammar and token classes.
import { classHighlighter, highlightTree } from "@lezer/highlight";
import { solidity } from "@replit/codemirror-lang-solidity";

export interface Token {
  from: number;
  to: number;
  cls: string;
}

export function tokens(source: string): Token[] {
  const out: Token[] = [];
  highlightTree(solidity.language.parser.parse(source), classHighlighter, (from, to, cls) =>
    out.push({ from, to, cls }),
  );
  return out;
}

export interface Segment {
  text: string;
  cls?: string;
  marked: boolean;
}

/** The text from @from to @to cut where tokens and the marked range start and end */
export function segments(source: string, toks: Token[], from: number, to: number, mark?: [number, number]): Segment[] {
  const cuts = new Set([from, to]);
  for (const t of toks) {
    if (t.to > from && t.from < to) cuts.add(Math.max(t.from, from)).add(Math.min(t.to, to));
  }
  if (mark) cuts.add(Math.min(Math.max(mark[0], from), to)).add(Math.min(Math.max(mark[1], from), to));
  const points = [...cuts].sort((a, b) => a - b);
  const out: Segment[] = [];
  for (let i = 0; i + 1 < points.length; i++) {
    const [a, b] = [points[i]!, points[i + 1]!];
    if (a === b) continue;
    out.push({
      text: source.slice(a, b),
      cls: toks.find((t) => t.from <= a && b <= t.to)?.cls,
      marked: mark !== undefined && mark[0] <= a && b <= mark[1],
    });
  }
  return out;
}
