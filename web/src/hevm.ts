import { ConsoleStdout, Directory, File, OpenFile, PreopenDirectory, WASI, type Inode } from "@bjorn3/browser_wasi_shim";

export interface RunResult {
  exitCode: number;
  stdout: string;
  stderr: string;
}

export type Mode = "exec" | "symbolic";

export interface Request {
  mode: Mode;
  code: string;
  calldata?: string;
  sig?: string;
}

export type Outcome =
  | { kind: "return"; data: string }
  | { kind: "revert"; data: string }
  | { kind: "counterexamples"; calldata: string[] }
  | { kind: "safe" }
  | { kind: "error"; message: string };

const hexRe = /^0x([0-9a-fA-F]{2})*$/;

/** Strips whitespace and adds a 0x prefix; throws unless what is left is an even number of hex digits */
export function normaliseHex(input: string, what: string): string {
  const s = input.replace(/\s+/g, "");
  const hex = s.startsWith("0x") || s.startsWith("0X") ? "0x" + s.slice(2) : "0x" + s;
  if (!hexRe.test(hex)) throw new Error(`${what} must be hex bytes, got '${input.trim()}'`);
  return hex.toLowerCase();
}

export function buildArgs(req: Request): string[] {
  const args = [req.mode, "--code", normaliseHex(req.code, "code")];
  if (req.mode === "exec" && req.calldata?.trim()) {
    args.push("--calldata", normaliseHex(req.calldata, "calldata"));
  }
  if (req.mode === "symbolic" && req.sig?.trim()) {
    args.push("--sig", req.sig.trim());
  }
  return args;
}

export function stripAnsi(s: string): string {
  return s.replace(/\x1b\[[0-9;]*m/g, "");
}

export function parseOutcome(mode: Mode, result: RunResult): Outcome {
  const out = stripAnsi(result.stdout);
  if (mode === "exec") {
    const m = /^"?(Return|Revert): (0x[0-9a-f]*)"?$/m.exec(out);
    if (m) return { kind: m[1] === "Return" ? "return" : "revert", data: m[2]! };
  } else {
    if (/^QED: No reachable property violations discovered/m.test(out)) return { kind: "safe" };
    if (/^Discovered the following \d+ counterexample/m.test(out)) {
      const calldata = [...out.matchAll(/^Calldata:\n\s+(0x[0-9a-f]*)/gm)].map((m) => m[1]!);
      return { kind: "counterexamples", calldata };
    }
  }
  const message = [stripAnsi(result.stderr), out].map((s) => s.trim()).filter(Boolean).join("\n");
  return { kind: "error", message: message || `hevm exited with code ${result.exitCode}` };
}

/** Paths and their contents, or null for an empty directory */
export type Files = Record<string, string | null>;

type Tree = Map<string, Tree | string>;

function inodes(tree: Tree): Map<string, Inode> {
  const enc = new TextEncoder();
  return new Map(
    [...tree].map(([name, t]) => [name, typeof t === "string" ? new File(enc.encode(t)) : new Directory(inodes(t))]),
  );
}

function treeOf(files: Files): Tree {
  const root: Tree = new Map();
  for (const [path, content] of Object.entries(files)) {
    const parts = path.split("/").filter(Boolean);
    let dir = root;
    parts.forEach((part, i) => {
      if (i === parts.length - 1 && content !== null) {
        dir.set(part, content);
      } else {
        let sub = dir.get(part);
        if (!(sub instanceof Map)) dir.set(part, (sub = new Map()));
        dir = sub;
      }
    });
  }
  return root;
}

/** Runs hevm.wasm, a WASI command, with the files in an in-memory filesystem at / */
export async function runHevm(module: WebAssembly.Module, args: string[], files: Files = {}): Promise<RunResult> {
  const stdout: string[] = [];
  const stderr: string[] = [];
  const wasi = new WASI(
    ["hevm", ...args],
    ["HOME=/", "PATH=/"],
    [
      new OpenFile(new File([])),
      ConsoleStdout.lineBuffered((l) => stdout.push(l)),
      ConsoleStdout.lineBuffered((l) => stderr.push(l)),
      new PreopenDirectory("/", inodes(treeOf(files))),
    ],
    { debug: false },
  );
  const instance = await WebAssembly.instantiate(module, {
    wasi_snapshot_preview1: wasi.wasiImport,
  });
  let exitCode: number;
  try {
    exitCode = wasi.start(instance as unknown as Parameters<WASI["start"]>[0]);
  } catch (e) {
    // a trap, e.g. the abort after an uncaught C++ exception in bitwuzla
    stderr.push(String(e));
    exitCode = 134;
  }
  return { exitCode, stdout: stdout.join("\n"), stderr: stderr.join("\n") };
}
