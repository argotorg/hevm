// The Equivalence tab: whether two compiled programs behave the same on every call.
import { describeCall, describeOutcome, signature } from "./abi";
import { compile, runHevm } from "./client";
import { $, button, el } from "./dom";
import { SolidityEditor } from "./editor";
import { eqExamples } from "./eqExamples";
import { parseEquivalence, type EqCounterexample } from "./eqOutput";
import { contractNames, eqArgs, eqPrograms, type EqMode, type EqProgram } from "./equivalence";
import { stripAnsi } from "./hevm";
import { newStats, onProgress, type Stats } from "./progress";
import type { Shared } from "./share";

type EqShared = Extract<Shared, { tab: "eq" }>;

export interface EqTabOptions {
  /** opens a program in the Bytecode tab, to run it on the calldata */
  openInBytecode(code: string, calldata: string): void;
}

const fmt = (secs: number) => (secs < 10 ? secs.toFixed(2) : secs.toFixed(1)) + "s";

export interface EqTab {
  /** what a link to the tab holds */
  shared(): EqShared;
  /** shows what a link holds, unless it names no example there is */
  open(s: EqShared): boolean;
  check(): void;
}

export function setupEquivalence(opts: EqTabOptions): EqTab {
  const form = $<HTMLFormElement>("eq-form");
  const example = $<HTMLSelectElement>("eq-example");
  const mode = $<HTMLSelectElement>("eq-mode");
  const pickA = $<HTMLSelectElement>("eq-a");
  const pickB = $<HTMLSelectElement>("eq-b");
  const labelA = $<HTMLElement>("eq-a-label");
  const fieldB = $<HTMLElement>("eq-b-field");
  const check = $<HTMLButtonElement>("eq-check");
  const status = $<HTMLElement>("eq-status");
  const progress = $<HTMLElement>("eq-progress");
  const results = $<HTMLElement>("eq-results");

  const showMode = () => {
    const two = mode.value === "contracts";
    fieldB.hidden = !two;
    labelA.textContent = two ? "Contract A" : "Contract";
  };

  // the contracts the source defines, keeping what was picked where it still exists
  const refreshContracts = (source: string, a?: string, b?: string) => {
    const names = contractNames(source);
    for (const [pick, want, fallback] of [[pickA, a, 0], [pickB, b, 1]] as const) {
      const keep = want ?? pick.value;
      pick.replaceChildren(...names.map((n) => new Option(n, n)));
      pick.value = names.includes(keep) ? keep : (names[fallback] ?? names[0] ?? "");
    }
    // comparing a contract with itself proves nothing
    if (pickB.value === pickA.value) pickB.value = names.find((n) => n !== pickA.value) ?? pickB.value;
  };

  const editor = new SolidityEditor($("eq-source"), "", (text) => refreshContracts(text));

  const load = (i: number) => {
    const ex = eqExamples[i]!;
    mode.value = ex.mode;
    editor.value = ex.source;
    refreshContracts(ex.source, ex.a, ex.b);
    showMode();
    results.replaceChildren();
    progress.hidden = true;
  };

  eqExamples.forEach((ex, i) => example.add(new Option(ex.name, String(i))));
  example.addEventListener("change", () => load(Number(example.value)));
  mode.addEventListener("change", showMode);
  load(0);

  const phaseLabel = (phase: string | undefined, a: string, b: string) =>
    ({
      "explore A": `Exploring every path of ${a}`,
      "explore B": `Exploring every path of ${b}`,
      "build-pairs": "Pairing up their end states",
      "check-pairs": "Asking the solver where they differ",
      replay: "Replaying the differences concretely",
      report: "Done",
    })[phase ?? ""] ?? "Starting hevm…";

  const renderProgress = (stats: Stats, label: string, running: boolean, elapsed: number) => {
    const bar = el("div", "bar");
    bar.classList.toggle("busy", running);
    bar.append(el("div", "fill"), el("span", "label", label));
    const counters = el("dl", "counters");
    const add = (k: string, v: string) => {
      const item = el("div");
      item.append(el("dt", undefined, k), el("dd", undefined, v));
      counters.append(item);
    };
    add("Paths", String(stats.paths));
    add("Branches", String(stats.forks));
    add("SMT queries", stats.queriesDone + (stats.queriesInFlight ? ` (+${stats.queriesInFlight} running)` : ""));
    add("Solver time", fmt(stats.solveSecs));
    add("Elapsed", fmt(elapsed));
    progress.replaceChildren(bar, counters);
    progress.hidden = false;
  };

  const renderCounterexample = (card: HTMLElement, c: EqCounterexample, a: EqProgram, b: EqProgram) => {
    const call = describeCall(c.calldata, a.abi, a.selectors);
    const outputs = (p: EqProgram) => {
      const selector = c.calldata.slice(2, 10);
      return p.abi.find((f) => p.selectors[signature(f)] === selector)?.outputs;
    };
    const dl = el("dl");
    dl.append(el("dt", undefined, "Input"), el("dd", "mono", call));
    if (call !== c.calldata) dl.append(el("dt", undefined, "Calldata"), el("dd", "mono raw", c.calldata));
    dl.append(el("dt", undefined, a.label), el("dd", undefined, c.a ? describeOutcome(c.a, outputs(a)) : "?"));
    dl.append(el("dt", undefined, b.label), el("dd", undefined, c.b ? describeOutcome(c.b, outputs(b)) : "?"));
    if (!c.validated) dl.append(el("dt"), el("dd", "muted", "could not be confirmed by running both concretely"));
    card.append(dl);
    if (c.difference) card.append(el("p", "muted", `hevm: ${c.difference}`));
    const actions = el("div", "card-actions");
    actions.append(
      button(`Run ${a.label} in Bytecode tab`, () => opts.openInBytecode(a.code, c.calldata)),
      button(`Run ${b.label} in Bytecode tab`, () => opts.openInBytecode(b.code, c.calldata)),
    );
    card.append(actions);
  };

  form.addEventListener("submit", async (e) => {
    e.preventDefault();
    check.disabled = true;
    results.replaceChildren();
    const started = performance.now();
    const elapsed = () => (performance.now() - started) / 1000;
    const stats = newStats();
    let label = "Compiling…";
    const clock = setInterval(() => renderProgress(stats, label, true, elapsed()), 250);
    renderProgress(stats, label, true, 0);
    try {
      status.textContent = "Compiling…";
      const prepared = await eqPrograms(compile, editor.value, mode.value as EqMode, pickA.value, pickB.value);
      if ("errors" in prepared) {
        status.textContent = `Compilation failed — ${fmt(elapsed())}`;
        progress.hidden = true;
        for (const err of prepared.errors) results.append(el("pre", "card fail", err.formatted));
        return;
      }
      const [a, b] = prepared.programs;
      status.textContent = "Checking…";
      label = phaseLabel(undefined, a.label, b.label);
      const run = await runHevm(eqArgs(a, b), undefined, (m) => {
        if ("progress" in m) {
          onProgress(stats, m.progress);
          label = phaseLabel(stats.phase, a.label, b.label);
        }
      });
      clearInterval(clock);
      const result = parseEquivalence(run.stdout);
      renderProgress(stats, "Done", false, elapsed());
      const verdict = { equivalent: "pass", different: "fail", unknown: "note" }[result.verdict];
      const card = el("article", `card ${verdict}`);
      const head = el("h3");
      head.append(el("span", `badge ${verdict}`, result.verdict.toUpperCase()), ` ${a.label} and ${b.label}`);
      card.append(head);
      if (result.verdict === "equivalent") {
        card.append(el("p", "muted", "They return the same, revert the same and write the same storage on every call."));
      } else if (result.verdict === "different") {
        card.append(el("p", "muted", result.counterexamples.length === 1 ? "On this input they differ:" : "On these inputs they differ:"));
      } else {
        card.append(el("p", "muted", "hevm could not decide whether they behave the same."));
      }
      for (const c of result.counterexamples) renderCounterexample(card, c, a, b);
      if (result.warnings.length) {
        card.append(el("p", "where", "Parts hevm could not explore:"));
        const list = el("ul", "warnings");
        for (const w of result.warnings) list.append(el("li", undefined, w));
        card.append(list);
      }
      if (result.verdict === "unknown" && !result.warnings.length && run.exitCode !== 0) {
        card.append(el("pre", undefined, stripAnsi(run.stderr || run.stdout).trim()));
      }
      results.append(card);
      status.textContent = `${result.verdict === "equivalent" ? "Equivalent" : result.verdict === "different" ? "Not equivalent" : "Undecided"} — ${fmt(elapsed())}`;
    } catch (err) {
      progress.hidden = true;
      status.textContent = "";
      results.append(el("pre", "card fail", String(err)));
    } finally {
      clearInterval(clock);
      check.disabled = false;
    }
  });

  return {
    shared() {
      const ex = eqExamples.find((e) =>
        e.source === editor.value && e.mode === mode.value && e.a === pickA.value && (e.mode !== "contracts" || e.b === pickB.value));
      return ex
        ? { tab: "eq", example: ex.name }
        : { tab: "eq", source: editor.value, mode: mode.value as EqMode, a: pickA.value, b: pickB.value };
    },
    open(s) {
      if ("example" in s) {
        const i = eqExamples.findIndex((e) => e.name === s.example);
        if (i < 0) return false;
        example.value = String(i);
        load(i);
        return true;
      }
      example.selectedIndex = -1;
      mode.value = s.mode;
      editor.value = s.source;
      refreshContracts(s.source, s.a, s.b);
      showMode();
      results.replaceChildren();
      progress.hidden = true;
      return true;
    },
    check: () => form.requestSubmit(),
  };
}
