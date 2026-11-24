// Statistics of a `hevm test` run, from its progress events as they come.
import type { ProgressEvent } from "./hevm";

export interface TestStats {
  name: string;
  paths: number;
  forks: number;
  queries: number;
  solveSecs: number;
  cex: number;
  secs?: number;
}

export interface Stats {
  /** functions to check, from the `Checking N function(s)` lines */
  total: number;
  tests: TestStats[];
  paths: number;
  forks: number;
  queriesDone: number;
  queriesInFlight: number;
  solveSecs: number;
  /** query results, e.g. sat or unsat, and how many there were */
  results: Record<string, number>;
  elapsed: number;
  finished: boolean;
  /** the phase hevm is in, e.g. "explore A" */
  phase?: string;
}

export function newStats(): Stats {
  return {
    total: 0,
    tests: [],
    paths: 0,
    forks: 0,
    queriesDone: 0,
    queriesInFlight: 0,
    solveSecs: 0,
    results: {},
    elapsed: 0,
    finished: false,
  };
}

export function onStdout(s: Stats, line: string) {
  const m = /^Checking (\d+) function\(s\) in contract /.exec(line);
  if (m) s.total += Number(m[1]);
}

export function onProgress(s: Stats, e: ProgressEvent) {
  s.elapsed = e.t;
  const current = s.tests.at(-1);
  const num = (k: string) => (typeof e[k] === "number" ? (e[k] as number) : 0);
  switch (e.ev) {
    case "phase-start":
      s.phase = String(e.phase);
      if (e.phase === "test") {
        s.tests.push({ name: String(e.test ?? ""), paths: 0, forks: 0, queries: 0, solveSecs: 0, cex: 0 });
      }
      break;
    case "fork":
      s.forks += 1;
      if (current) current.forks += 1;
      break;
    case "path-end":
      s.paths += 1;
      if (current) current.paths += 1;
      break;
    case "query-start":
      s.queriesInFlight += 1;
      break;
    case "query-end": {
      s.queriesInFlight = Math.max(0, s.queriesInFlight - 1);
      s.queriesDone += 1;
      s.solveSecs += num("solveSecs");
      const result = String(e.result ?? "unknown").split(" ")[0]!;
      s.results[result] = (s.results[result] ?? 0) + 1;
      if (current) {
        current.queries += 1;
        current.solveSecs += num("solveSecs");
      }
      break;
    }
    case "phase-end":
      if (e.phase === "test" && current) {
        current.secs = num("secs");
        current.cex = num("cex");
      }
      break;
    case "end":
      s.finished = true;
      break;
  }
}

/** Functions finished checking */
export function testsDone(s: Stats): number {
  return s.tests.filter((t) => t.secs !== undefined).length;
}
