// The runtime: the only module with side effects. It sends commands to hevm,
// feeds the answers through `update`, and renders the model with `view`.
import { api, type View } from "./api";
import { keyAction, shortcuts } from "./keys";
import { commandEnabled, initialModel, update, type Model, type Msg } from "./model";
import { render, h } from "./vdom";
import { resultText } from "./highlight";
import * as view from "./view";

function byId<T extends HTMLElement>(id: string): T {
  const node = document.getElementById(id);
  if (node === null) throw new Error(`the page has no #${id}`);
  return node as T;
}

export class App {
  private model: Model = initialModel;
  private history: string[] = [];
  private historyPos = 0;
  private readonly input = byId<HTMLInputElement>("command");
  private readonly breakInput = byId<HTMLInputElement>("break-input");

  async start(): Promise<void> {
    this.input.addEventListener("keydown", (e) => this.onConsoleKey(e));
    this.breakInput.addEventListener("keydown", (e) => {
      if (e.key === "Enter" && this.breakInput.value.trim() !== "") {
        this.run(`break ${this.breakInput.value.trim()}`);
        this.breakInput.value = "";
      }
    });
    document.addEventListener("keydown", (e) => this.onKey(e));
    for (const button of document.querySelectorAll<HTMLButtonElement>("[data-command]")) {
      button.addEventListener("click", () => this.run(button.dataset["command"] ?? ""));
    }
    try {
      this.dispatch({ type: "view", view: await api.state() });
    } catch (e) {
      this.dispatch({ type: "failed", error: String(e) });
    }
    await this.refreshSide();
  }

  readonly run = (command: string): void => {
    void this.execute(command);
  };

  readonly copy = (text: string): void => {
    navigator.clipboard.writeText(text).then(
      () => this.dispatch({ type: "note", text: `Copied ${text.length} characters.` }),
      (e: unknown) => this.dispatch({ type: "failed", error: `Cannot copy: ${String(e)}` }),
    );
  };

  private dispatch(msg: Msg): void {
    this.model = update(this.model, msg);
    this.draw();
  }

  private async execute(command: string): Promise<void> {
    if (this.model.busy) {
      this.dispatch({ type: "failed", error: "Still working on the previous command." });
      return;
    }
    this.dispatch({ type: "started", command });
    // the server answers /progress while the command runs
    const poller = window.setInterval(() => void this.poll(), 500);
    try {
      this.dispatch({ type: "view", view: await api.command(command) });
    } catch (e) {
      this.dispatch({ type: "failed", error: String(e) });
    } finally {
      window.clearInterval(poller);
      this.dispatch({ type: "finished" });
      await this.refreshSide();
    }
  }

  private async poll(): Promise<void> {
    try {
      this.dispatch({ type: "progress", progress: await api.progress() });
    } catch {
      // a lost server shows when the command fails
    }
  }

  private async refreshSide(): Promise<void> {
    try {
      const [stats, progress, trace] = await Promise.all([api.stats(), api.progress(), api.trace()]);
      this.dispatch({ type: "stats", stats });
      this.dispatch({ type: "progress", progress });
      this.dispatch({ type: "trace", trace });
    } catch (e) {
      this.dispatch({ type: "failed", error: String(e) });
    }
  }

  private draw(): void {
    const m = this.model;
    document.body.classList.toggle("busy", m.busy);
    const v: View | null = m.view;
    if (v !== null) {
      render(byId("status"), view.statusBar(v));
      render(byId("code"), view.codePane(v, this.run));
      render(byId("source"), view.sourcePane(v));
      render(byId("stack"), view.stackPane(v, this.copy));
      render(byId("memory"), view.memoryPane(v, this.run));
      render(byId("storage"), view.storagePane(v, this.copy));
      render(byId("branch"), view.branchPane(v, this.run));
      render(byId("breakpoints"), view.breakpointList(v, this.run));
      render(byId("warnings-list"), view.warningsPane(v));
      byId("warnings").hidden = v.warnings.length === 0;
      byId("result").textContent = v.result === null ? "" : resultText(v.result);
      byId("code").querySelector(".current")?.scrollIntoView({ block: "nearest" });
      byId("source").querySelector(".current")?.scrollIntoView({ block: "center" });
    }
    for (const button of document.querySelectorAll<HTMLButtonElement>("[data-command]")) {
      button.disabled = !commandEnabled(v, button.dataset["command"] ?? "");
    }
    render(byId("stats"), view.statsPane(m.stats));
    render(byId("progress"), view.progressPane(m.progress, m.busy));
    render(byId("trace"), view.tracePane(m.trace));
    const log = byId("log");
    render(log, view.logPane(m.log));
    log.scrollTop = log.scrollHeight;
  }

  private onConsoleKey(e: KeyboardEvent): void {
    if (e.key === "Enter") {
      const command = this.input.value.trim();
      this.input.value = "";
      if (command === "") return;
      this.history.push(command);
      this.historyPos = this.history.length;
      this.run(command);
    } else if (e.key === "ArrowUp" && this.historyPos > 0) {
      this.historyPos--;
      this.input.value = this.history[this.historyPos] ?? "";
      e.preventDefault();
    } else if (e.key === "ArrowDown" && this.historyPos < this.history.length) {
      this.historyPos++;
      this.input.value = this.history[this.historyPos] ?? "";
      e.preventDefault();
    } else if (e.key === "Escape") {
      this.input.blur();
    }
  }

  private onKey(e: KeyboardEvent): void {
    const target = e.target as HTMLElement | null;
    const action = keyAction(
      { key: e.key, ctrl: e.ctrlKey || e.metaKey || e.altKey, inInput: target?.tagName === "INPUT" },
      this.model.view?.branch !== null && this.model.view?.branch !== undefined,
    );
    if (action === null) return;
    e.preventDefault();
    if ("run" in action) {
      if (commandEnabled(this.model.view, action.run)) this.run(action.run);
    }
    else if ("focusConsole" in action) this.input.focus();
    else void this.showHelp();
  }

  private async showHelp(): Promise<void> {
    const help = await api.help();
    const keys = [...Object.entries(shortcuts).map(([k, c]) => `${k}   ${c}`), "0-9 pick that branch option", ":   type a command", "?   this help"];
    const dialog = byId<HTMLDialogElement>("help");
    render(dialog, [
      h("h2", {}, "Keys"),
      h("pre", {}, keys.join("\n")),
      h("h2", {}, "Commands"),
      h("pre", {}, help.commands.join("\n")),
      h("p", { class: "pane-note" }, "Click anywhere to close."),
    ]);
    dialog.showModal();
  }
}
