// Single-key shortcuts, as in the old TTY debugger where they overlap
export const shortcuts: Record<string, string> = {
  s: "step",
  n: "next",
  o: "over",
  u: "out",
  c: "continue",
  b: "back",
  B: "back-line",
  r: "restart",
  t: "branch true",
  f: "branch false",
};

export type KeyAction = { run: string } | { focusConsole: true } | { help: true } | null;

export interface KeyPress {
  key: string;
  ctrl: boolean;
  inInput: boolean;
}

// What a key press does; digits pick a branch option while one is pending
export function keyAction(press: KeyPress, branchPending: boolean): KeyAction {
  if (press.inInput || press.ctrl) return null;
  if (press.key === ":" || press.key === "/") return { focusConsole: true };
  if (press.key === "?") return { help: true };
  const command = shortcuts[press.key];
  if (command !== undefined) return { run: command };
  if (branchPending && /^[0-9]$/.test(press.key)) return { run: `branch ${press.key}` };
  return null;
}
