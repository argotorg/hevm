// Reads the output of `hevm equivalence`.
import { stripAnsi } from "./hevm";

export interface EqCounterexample {
  calldata: string;
  difference: string;
  /** whether running A and B concretely on it shows the difference */
  validated: boolean;
  a?: string;
  b?: string;
}

export interface EqResult {
  verdict: "equivalent" | "different" | "unknown";
  counterexamples: EqCounterexample[];
  /** why parts could not be explored, e.g. "2x -> Max Iterations Reached in ..." */
  warnings: string[];
}

export function parseEquivalence(output: string): EqResult {
  const lines = stripAnsi(output).split("\n");
  const result: EqResult = { verdict: "unknown", counterexamples: [], warnings: [] };
  let cex: EqCounterexample | undefined;
  let replayed = false;
  let warning = false;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!;
    let m: RegExpExecArray | null;
    if (/\[PASS\] Contracts behave equivalently/.test(line)) result.verdict = "equivalent";
    else if (/\[FAIL\] Contracts do not behave equivalently/.test(line)) result.verdict = "different";
    if (/\[WARNING\]/.test(line)) {
      warning = true;
    } else if (warning && (m = /^\s+(\d+x -> .*)$/.exec(line))) {
      result.warnings.push(m[1]!);
    } else {
      warning = false;
    }
    if (line === "-----") {
      cex = { calldata: "", difference: "", validated: false };
      result.counterexamples.push(cex);
      replayed = false;
    } else if (!cex) {
      continue;
    } else if (line === "Calldata:") {
      cex.calldata = lines[++i]?.trim() ?? "";
    } else if ((m = /^Difference: (.*)$/.exec(line))) {
      cex.difference = m[1]!;
    } else if ((m = /^Concrete replay: \[(.*)\]/.exec(line))) {
      cex.validated = m[1] === "validated";
      replayed = true;
    } else if (replayed && (m = /^ {2}([AB]): (.*)$/.exec(line))) {
      cex[m[1] === "A" ? "a" : "b"] = m[2]!;
    }
  }
  return result;
}
