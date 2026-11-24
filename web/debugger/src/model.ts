// The frontend's state and how messages change it. Pure: no DOM, no network.
import type { Progress, StatsView, View } from "./api";

export type LogKind = "command" | "message" | "output" | "error";

export interface LogEntry {
  kind: LogKind;
  text: string;
}

export interface Model {
  view: View | null;
  stats: StatsView | null;
  progress: Progress | null;
  trace: string | null;
  busy: boolean;
  log: LogEntry[];
}

export type Msg =
  | { type: "started"; command: string }
  | { type: "view"; view: View }
  | { type: "stats"; stats: StatsView }
  | { type: "progress"; progress: Progress }
  | { type: "trace"; trace: string }
  | { type: "failed"; error: string }
  | { type: "note"; text: string }
  | { type: "finished" };

export const maxLog = 500;

export const initialModel: Model = { view: null, stats: null, progress: null, trace: null, busy: false, log: [] };

function logged(model: Model, ...entries: LogEntry[]): LogEntry[] {
  return [...model.log, ...entries].slice(-maxLog);
}

export function update(model: Model, msg: Msg): Model {
  switch (msg.type) {
    case "started":
      return { ...model, busy: true, log: logged(model, { kind: "command", text: `> ${msg.command}` }) };
    case "view": {
      const entries: LogEntry[] = [];
      // a command's output and message go to the log; the first view has only a greeting
      if (msg.view.output !== null) entries.push({ kind: "output", text: msg.view.output });
      if (msg.view.message !== "") entries.push({ kind: "message", text: msg.view.message });
      return { ...model, view: msg.view, log: logged(model, ...entries) };
    }
    case "stats":
      return { ...model, stats: msg.stats };
    case "progress":
      return { ...model, progress: msg.progress };
    case "trace":
      return { ...model, trace: msg.trace };
    case "failed":
      return { ...model, log: logged(model, { kind: "error", text: msg.error }) };
    case "note":
      return { ...model, log: logged(model, { kind: "message", text: msg.text }) };
    case "finished":
      return { ...model, busy: false };
  }
}

// Breakpoints on a pc, from the server's descriptions like "pc 0x2a"
export function pcBreakpoints(view: View): Map<number, number> {
  const found = new Map<number, number>();
  view.breakpoints.forEach((b, i) => {
    const m = /^pc (0x[0-9a-f]+)$/.exec(b);
    if (m?.[1] !== undefined) found.set(parseInt(m[1], 16), i);
  });
  return found;
}

// The argument `branch` takes for an option: false/true for two-way branches, else its index
export function branchArgument(options: string[], index: number): string {
  return options.length === 2 && options[0] === "false" ? (options[index] ?? String(index)) : String(index);
}

const forward = new Set(["step", "next", "over", "out", "continue"]);
const backward = new Set(["back", "back-line", "restart"]);

// Whether a toolbar command can do anything: nothing runs past the end or a pending
// branch, and nothing goes back from the first step
export function commandEnabled(view: View | null, command: string): boolean {
  if (view === null) return false;
  if (forward.has(command)) return view.status === "running";
  if (backward.has(command)) return view.step > 0;
  return true;
}
