// The server's answers, parsed as the page parses them
import { help, progress, stats, trace, view, type Progress, type StatsView, type View } from "../src/api";
import helpJson from "./fixtures/help.json";
import progressIdleJson from "./fixtures/progress-idle.json";
import progressRunningJson from "./fixtures/progress-running.json";
import stateBranchJson from "./fixtures/state-branch.json";
import stateBreakpointJson from "./fixtures/state-breakpoint.json";
import stateConcreteJson from "./fixtures/state-concrete.json";
import stateHaltedJson from "./fixtures/state-halted.json";
import statsJson from "./fixtures/stats.json";
import traceJson from "./fixtures/trace.json";

export const raw = {
  help: helpJson,
  progressIdle: progressIdleJson,
  progressRunning: progressRunningJson,
  stateBranch: stateBranchJson,
  stateBreakpoint: stateBreakpointJson,
  stateConcrete: stateConcreteJson,
  stateHalted: stateHaltedJson,
  stats: statsJson,
  trace: traceJson,
};

export const states: Record<string, View> = {
  branch: view.parse(stateBranchJson),
  breakpoint: view.parse(stateBreakpointJson),
  concrete: view.parse(stateConcreteJson),
  halted: view.parse(stateHaltedJson),
};
export const statsFixture: StatsView = stats.parse(statsJson);
export const progressRunning: Progress = progress.parse(progressRunningJson);
export const progressIdle: Progress = progress.parse(progressIdleJson);
export const helpFixture = help.parse(helpJson);
export const traceFixture: string = trace.parse(traceJson).trace;

// A state with changes to the concrete fixture, for cases the server's fixtures do not cover
export function stateWith(changes: Partial<View>): View {
  return { ...states["concrete"]!, ...changes };
}
