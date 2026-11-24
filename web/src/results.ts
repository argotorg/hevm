// Reads `hevm test` output into results per test function.
import { stripAnsi } from "./hevm";

export interface Location {
  file: string;
  line: number;
  column: number;
  code: string;
}

export interface Counterexample {
  validated: boolean | null;
  /** of an invariant: the calls that lead to the state it fails in */
  calls?: string[];
  calldata: string;
  /** the calldata as hex */
  raw?: string;
  result: string;
  at?: Location;
}

export interface TestResult {
  contract: string;
  name: string;
  status: "pass" | "fail" | "running";
  counterexamples: Counterexample[];
  notes: string[];
  /** what a pass covered, e.g. "7 states, up to 2 calls deep" */
  detail?: string;
}

export function parseTestOutput(stdout: string): TestResult[] {
  const results: TestResult[] = [];
  let contract = "";
  let current: TestResult | undefined;
  let cex: Counterexample | undefined;
  let inCalls = false;
  for (const raw of stripAnsi(stdout).split("\n")) {
    const line = raw.trimEnd();
    let m: RegExpExecArray | null;
    if (cex?.calls && inCalls && (m = /^ {10,}(\S.*)$/.exec(line))) {
      cex.calls.push(m[1]!);
      continue;
    }
    inCalls = false;
    if ((m = /^Checking \d+ function\(s\) in contract (.+)$/.exec(line))) {
      contract = m[1]!;
    } else if ((m = /^\[RUNNING\] (.+)$/.exec(line))) {
      current = { contract, name: m[1]!, status: "running", counterexamples: [], notes: [] };
      results.push(current);
      cex = undefined;
    } else if (!current) {
      continue;
    } else if ((m = /^\s+Counterexample:\s*(.*)$/.exec(line))) {
      cex = {
        validated: /\[validated\]/.test(m[1]!) ? true : /\[not reproducible\]/.test(m[1]!) ? false : null,
        calldata: "",
        result: "",
      };
      current.counterexamples.push(cex);
    } else if (cex && (m = /^\s+calls:\s+(.*)$/.exec(line))) {
      cex.calls = [m[1]!];
      inCalls = true;
    } else if (cex && (m = /^\s+calldata: (.*)$/.exec(line))) {
      cex.calldata = m[1]!;
    } else if (cex && (m = /^\s+raw:\s+(0x[0-9a-f]*)$/.exec(line))) {
      cex.raw = m[1]!;
    } else if (cex && (m = /^\s+result:\s+(.*)$/.exec(line))) {
      cex.result = m[1]!;
    } else if (cex && (m = /^\s+at:\s+(.+?):(\d+):(\d+): (.*)$/.exec(line))) {
      cex.at = { file: m[1]!, line: Number(m[2]), column: Number(m[3]), code: m[4]! };
    } else if ((m = /^\s+\[(PASS|FAIL)\] \S+(?: \((.*)\))?$/.exec(line))) {
      current.status = m[1] === "PASS" ? "pass" : "fail";
      if (m[2]) current.detail = m[2];
      cex = undefined;
    } else if ((m = /^\s+\[(WARNING|CAVEAT)\] (.*)$/.exec(line))) {
      current.notes.push(m[2]!);
    }
  }
  return results;
}

/** Numbers of 2^64 and more in hex, where their bit patterns show */
export function readableNumbers(text: string): string {
  return text.replace(/\b\d{20,}\b/g, (n) => (BigInt(n) >= 1n << 64n ? "0x" + BigInt(n).toString(16) : n));
}

const panics: Record<number, string> = {
  0x01: "assertion failed",
  0x11: "arithmetic overflow or underflow",
  0x12: "division or modulo by zero",
  0x21: "invalid enum value",
  0x22: "invalid storage byte array",
  0x31: "pop from an empty array",
  0x32: "array index out of bounds",
  0x41: "too much memory allocated",
  0x51: "call to an uninitialized function",
};

/** Explains a `Revert: 0x...` result that is a Panic(uint256) or an Error(string) */
export function describeResult(result: string): string {
  if (result === "Unrecognized opcode: 254") return "INVALID opcode: a failed assert, before Solidity 0.8";
  const m = /^Revert: 0x([0-9a-f]*)$/.exec(result);
  if (!m) return result;
  const data = m[1]!;
  if (data.startsWith("4e487b71") && data.length === 8 + 64) {
    const code = parseInt(data.slice(8), 16);
    return `Panic(0x${code.toString(16).padStart(2, "0")}): ${panics[code] ?? "unknown panic"}`;
  }
  if (data.startsWith("08c379a0") && data.length >= 8 + 128) {
    const len = parseInt(data.slice(8 + 64, 8 + 128), 16);
    const bytes = data.slice(8 + 128, 8 + 128 + 2 * len).match(/../g) ?? [];
    return `Error("${new TextDecoder().decode(new Uint8Array(bytes.map((b) => parseInt(b, 16))))}")`;
  }
  return data ? `Revert: 0x${data}` : "Revert";
}
