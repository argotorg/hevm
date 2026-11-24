// The debugger server's JSON (src/EVM/Debugger.hs, src/EVM/Progress.hs), checked
// when it arrives. The fixtures in web/test/fixtures are real answers of the
// server: the TypeScript tests parse them with these schemas, and the Haskell
// test "web-fixtures-match-server" checks that the server still answers that way.
import { arr, bool, lit, nullable, num, obj, oneOf, optional, record, str, unknownValue, type Infer, type Schema } from "./schema";

export const codeLine = obj({ pc: num, op: str, arg: nullable(str), current: bool });
export const sourceLine = obj({ line: num, text: str, current: bool });
export const sourceView = obj({ file: str, line: num, lines: arr(sourceLine) });
export const branchView = obj({ condition: nullable(str), options: arr(str) });

// A literal word as hex, anything else as an expression
export const word = oneOf(obj({ hex: str }), obj({ expr: str }));
export type Word = Infer<typeof word>;

export const view = obj({
  mode: lit("concrete", "symbolic"),
  step: num,
  status: lit("running", "branch", "halted"),
  result: nullable(obj({ outcome: lit("success", "revert", "failure", "unfinished"), output: nullable(word), problem: nullable(str) })),
  pc: num,
  op: str,
  contract: str,
  codeContract: str,
  depth: num,
  gas: nullable(num),
  codeName: nullable(str),
  code: arr(codeLine),
  stack: arr(word),
  memorySize: num,
  memory: word,
  source: nullable(sourceView),
  generatedCode: bool,
  storage: arr(obj({ address: word, current: bool, initial: lit("known", "unknown"), slots: arr(obj({ slot: word, value: word })) })),
  pathConditions: num,
  branch: nullable(branchView),
  choices: arr(str),
  breakpoints: arr(str),
  message: str,
  output: nullable(str),
  branchMode: lit("solver", "explorer", "checked"),
  simplified: bool,
  warnings: arr(str),
});
export type View = Infer<typeof view>;

export const stats = obj({
  step: num,
  snapshotCount: num,
  counters: obj({
    commands: num,
    commandSecs: num,
    opcodes: num,
    replayedOpcodes: num,
    queries: num,
    querySecs: num,
    branchesOffered: num,
    branchesTaken: num,
    staticDecisions: num,
    infeasibleOptions: num,
    breakpointHits: num,
  }),
});
export type StatsView = Infer<typeof stats>;

const inFlightQuery = obj({ secs: num, solving: bool, kind: optional(str), pc: optional(num) });
const queryResultCount = obj({ kind: str, result: str, count: num, waitSecs: num, solveSecs: num });
const hotSpot = obj({ addr: str, pc: num, queries: num, solveSecs: num, forks: num });

export const runningProgress = obj({
  running: lit(true),
  elapsedSecs: num,
  phase: obj({ name: str, done: num, total: num }),
  paths: obj({ done: num, partial: num }),
  tasks: num,
  workers: arr(record(unknownValue)),
  queries: obj({ done: num, inFlight: arr(inFlightQuery), byResult: arr(queryResultCount) }),
  hottest: arr(hotSpot),
  phases: arr(record(unknownValue)),
});
export const progress = oneOf(runningProgress, obj({ running: lit(false) }));
export type Progress = Infer<typeof progress>;

export const help = obj({ commands: arr(str), api: arr(str) });
export const trace = obj({ trace: str });

export class ApiError extends Error {
  override name = "ApiError";
}

async function request<T>(schema: Schema<T>, method: "GET" | "POST", path: string, body?: string): Promise<T> {
  let response: Response;
  try {
    response = await fetch(path, body === undefined ? { method } : { method, body });
  } catch (e) {
    throw new ApiError(`cannot reach hevm: ${String(e)}`);
  }
  if (!response.ok) throw new ApiError(`${method} ${path}: ${response.status} ${await response.text()}`);
  try {
    return schema.parse(await response.json());
  } catch (e) {
    throw new ApiError(`${method} ${path} answered unexpectedly, is this the hevm the page came with? ${String(e)}`);
  }
}

export const api = {
  state: (): Promise<View> => request(view, "GET", "/state"),
  command: (command: string): Promise<View> => request(view, "POST", "/command", JSON.stringify({ command })),
  stats: (): Promise<StatsView> => request(stats, "GET", "/stats"),
  progress: (): Promise<Progress> => request(progress, "GET", "/progress"),
  help: (): Promise<Infer<typeof help>> => request(help, "GET", "/help"),
  trace: async (): Promise<string> => (await request(trace, "GET", "/trace")).trace,
};
