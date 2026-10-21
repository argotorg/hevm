// src/schema.ts
var SchemaError = class extends Error {
  name = "SchemaError";
};
function fail(path, expected, value) {
  throw new SchemaError(`${path || "value"}: expected ${expected}, got ${JSON.stringify(value)?.slice(0, 80)}`);
}
function primitive(name, test) {
  return {
    parse(value, path = "") {
      if (!test(value)) fail(path, name, value);
      return value;
    }
  };
}
var str = primitive("a string", (v) => typeof v === "string");
var num = primitive("a number", (v) => typeof v === "number");
var bool = primitive("a boolean", (v) => typeof v === "boolean");
var unknownValue = primitive("anything", () => true);
function lit(...values) {
  return primitive(`one of ${values.join(", ")}`, (v) => values.includes(v));
}
function nullable(inner) {
  return { parse: (value, path = "") => value === null ? null : inner.parse(value, path) };
}
function optional(inner) {
  return { parse: (value, path = "") => value === void 0 ? void 0 : inner.parse(value, path) };
}
function arr(inner) {
  return {
    parse(value, path = "") {
      if (!Array.isArray(value)) fail(path, "an array", value);
      return value.map((v, i) => inner.parse(v, `${path}[${i}]`));
    }
  };
}
function obj(shape) {
  return {
    shape,
    parse(value, path = "") {
      if (typeof value !== "object" || value === null || Array.isArray(value)) fail(path, "an object", value);
      const record2 = value;
      const out = { ...record2 };
      for (const [k, s] of Object.entries(shape)) {
        out[k] = s.parse(record2[k], path === "" ? k : `${path}.${k}`);
      }
      return out;
    }
  };
}
function record(inner) {
  return {
    parse(value, path = "") {
      if (typeof value !== "object" || value === null || Array.isArray(value)) fail(path, "an object", value);
      return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, inner.parse(v, `${path}.${k}`)]));
    }
  };
}
function oneOf(a, b) {
  return {
    parse(value, path = "") {
      try {
        return a.parse(value, path);
      } catch (e) {
        if (!(e instanceof SchemaError)) throw e;
        return b.parse(value, path);
      }
    }
  };
}

// src/api.ts
var codeLine = obj({ pc: num, op: str, current: bool });
var sourceLine = obj({ line: num, text: str, current: bool });
var sourceView = obj({ file: str, line: num, lines: arr(sourceLine) });
var branchView = obj({ condition: nullable(str), options: arr(str) });
var view = obj({
  mode: lit("concrete", "symbolic"),
  step: num,
  status: lit("running", "branch", "halted"),
  result: nullable(str),
  pc: num,
  op: str,
  contract: str,
  codeContract: str,
  depth: num,
  gas: nullable(num),
  code: arr(codeLine),
  stack: arr(str),
  memorySize: num,
  memory: str,
  source: nullable(sourceView),
  pathConditions: num,
  branch: nullable(branchView),
  choices: arr(str),
  breakpoints: arr(str),
  message: str,
  output: nullable(str),
  branchMode: lit("solver", "explorer", "checked"),
  simplified: bool,
  warnings: arr(str),
  merging: bool
});
var stats = obj({
  step: num,
  snapshotCount: num,
  counters: obj({
    commands: num,
    commandSecs: num,
    opcodes: num,
    replayedOpcodes: num,
    queries: num,
    querySecs: num,
    branchQueries: num,
    solutionQueries: num,
    fetchQueries: num,
    otherQueries: num,
    branchesOffered: num,
    branchesTaken: num,
    staticDecisions: num,
    staticWrong: num,
    staticMissed: num,
    staticInconclusive: num,
    breakpointHits: num
  })
});
var inFlightQuery = obj({ secs: num, solving: bool, kind: optional(str), pc: optional(num) });
var queryResultCount = obj({ kind: str, result: str, count: num, waitSecs: num, solveSecs: num });
var hotSpot = obj({ addr: str, pc: num, queries: num, solveSecs: num, forks: num });
var runningProgress = obj({
  running: lit(true),
  elapsedSecs: num,
  phase: obj({ name: str, done: num, total: num }),
  paths: obj({ done: num, partial: num }),
  tasks: num,
  workers: arr(record(unknownValue)),
  queries: obj({ done: num, inFlight: arr(inFlightQuery), byResult: arr(queryResultCount) }),
  hottest: arr(hotSpot),
  phases: arr(record(unknownValue))
});
var progress = oneOf(runningProgress, obj({ running: lit(false) }));
var help = obj({ commands: arr(str), api: arr(str) });
var ApiError = class extends Error {
  name = "ApiError";
};
async function request(schema, method, path, body) {
  let response;
  try {
    response = await fetch(path, body === void 0 ? { method } : { method, body });
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
var api = {
  state: () => request(view, "GET", "/state"),
  command: (command) => request(view, "POST", "/command", JSON.stringify({ command })),
  stats: () => request(stats, "GET", "/stats"),
  progress: () => request(progress, "GET", "/progress"),
  help: () => request(help, "GET", "/help")
};

// src/keys.ts
var shortcuts = {
  s: "step",
  n: "next",
  o: "over",
  u: "out",
  c: "continue",
  b: "back",
  B: "back-line",
  r: "restart",
  t: "branch true",
  f: "branch false"
};
function keyAction(press, branchPending) {
  if (press.inInput || press.ctrl) return null;
  if (press.key === ":" || press.key === "/") return { focusConsole: true };
  if (press.key === "?") return { help: true };
  const command = shortcuts[press.key];
  if (command !== void 0) return { run: command };
  if (branchPending && /^[0-9]$/.test(press.key)) return { run: `branch ${press.key}` };
  return null;
}

// src/model.ts
var maxLog = 500;
var initialModel = { view: null, stats: null, progress: null, busy: false, log: [] };
function logged(model, ...entries) {
  return [...model.log, ...entries].slice(-maxLog);
}
function update(model, msg) {
  switch (msg.type) {
    case "started":
      return { ...model, busy: true, log: logged(model, { kind: "command", text: `> ${msg.command}` }) };
    case "view": {
      const entries = [];
      if (msg.view.output !== null) entries.push({ kind: "output", text: msg.view.output });
      if (msg.view.message !== "") entries.push({ kind: "message", text: msg.view.message });
      return { ...model, view: msg.view, log: logged(model, ...entries) };
    }
    case "stats":
      return { ...model, stats: msg.stats };
    case "progress":
      return { ...model, progress: msg.progress };
    case "failed":
      return { ...model, log: logged(model, { kind: "error", text: msg.error }) };
    case "finished":
      return { ...model, busy: false };
  }
}
function pcBreakpoints(view2) {
  const found = /* @__PURE__ */ new Map();
  view2.breakpoints.forEach((b, i) => {
    const m = /^pc (0x[0-9a-f]+)$/.exec(b);
    if (m?.[1] !== void 0) found.set(parseInt(m[1], 16), i);
  });
  return found;
}
function branchArgument(options, index) {
  return options.length === 2 && options[0] === "true" ? options[index] ?? String(index) : String(index);
}

// src/vdom.ts
function h(tag, props = {}, ...children) {
  const kids = [];
  for (const c of children) {
    if (c === null || c === void 0 || c === false) continue;
    kids.push(typeof c === "object" ? c : text(String(c)));
  }
  return { tag, props, children: kids };
}
function text(s) {
  return { tag: "#text", props: { text: s }, children: [] };
}
function toDom(node) {
  if (node.tag === "#text") return document.createTextNode(String(node.props["text"] ?? ""));
  const el = document.createElement(node.tag);
  for (const [k, v] of Object.entries(node.props)) {
    if (v === void 0) continue;
    if (k === "onClick" && typeof v === "function") el.addEventListener("click", v);
    else if (typeof v === "string") el.setAttribute(k, v);
  }
  for (const c of node.children) el.append(toDom(c));
  return el;
}
function render(container, nodes) {
  container.replaceChildren(...nodes.map(toDom));
}

// src/view.ts
function hex(n) {
  return "0x" + n.toString(16);
}
function fixed(n, digits) {
  return Number.isInteger(n) ? String(n) : n.toFixed(digits);
}
var badge = (label, cls) => h("span", { class: `badge ${cls}` }, label);
function statusBar(v) {
  return [
    h("span", { class: "step" }, `step ${v.step}`),
    badge(v.status, `status-${v.status}`),
    badge(v.mode, "mode"),
    h("span", { class: "where" }, `pc ${hex(v.pc)} `, h("b", {}, v.op)),
    h("span", { class: "meta" }, `depth ${v.depth}`),
    v.gas !== null && h("span", { class: "meta" }, `gas ${v.gas}`),
    h("span", { class: "contract", title: `code of ${v.codeContract}` }, v.contract),
    v.branchMode !== "solver" && badge(`branches: ${v.branchMode}`, "setting"),
    v.merging && badge("merging", "setting"),
    !v.simplified && badge("not simplified", "setting")
  ].filter((n) => n !== false);
}
function codePane(v, run) {
  const breaks = pcBreakpoints(v);
  return v.code.map((line) => {
    const bp = breaks.get(line.pc);
    const cls = ["code-line", line.current ? "current" : "", bp !== void 0 ? "has-break" : ""].filter(Boolean).join(" ");
    return h(
      "div",
      {
        class: cls,
        title: bp !== void 0 ? "click to delete the breakpoint" : "click to break here",
        onClick: () => run(bp !== void 0 ? `delete ${bp}` : `break pc ${hex(line.pc)}`)
      },
      h("span", { class: "gutter" }, bp !== void 0 ? "\u25CF" : line.current ? "\u25B6" : ""),
      h("span", { class: "addr" }, hex(line.pc)),
      h("span", { class: "op" }, line.op)
    );
  });
}
function sourcePane(v) {
  if (v.source === null) {
    return [h("div", { class: "empty" }, "No source map for this code. Run hevm in the project root, with its build output.")];
  }
  return [
    h("div", { class: "file" }, `${v.source.file}:${v.source.line}`),
    ...v.source.lines.map(
      (l) => h("div", { class: l.current ? "src-line current" : "src-line" }, h("span", { class: "lineno" }, l.line), h("span", { class: "text" }, l.text))
    )
  ];
}
function stackPane(v) {
  if (v.stack.length === 0) return [h("div", { class: "empty" }, "empty")];
  return v.stack.map((word, i) => h("div", { class: "stack-item" }, h("span", { class: "index" }, i), h("pre", { class: "word" }, word)));
}
function memoryPane(v, run) {
  return [
    h(
      "div",
      { class: "pane-note" },
      `${v.memorySize} bytes`,
      v.memorySize > 128 && " \xB7 first 128 shown ",
      v.memorySize > 128 && h("button", { type: "button", class: "small", onClick: () => run(`memory 0 ${Math.min(v.memorySize, 65536)}`) }, "show all")
    ),
    v.memorySize > 0 && h("pre", { class: "memory" }, v.memory)
  ].filter((n) => n !== false);
}
function branchPane(v, run) {
  if (v.branch === null) {
    return [
      h("div", { class: "empty" }, v.mode === "symbolic" ? "No branch pending." : "Concrete run: no symbolic branches."),
      ...v.choices.length > 0 ? [h("div", { class: "pane-note" }, "Taken so far:"), ...v.choices.map((c) => h("div", { class: "choice" }, c))] : []
    ];
  }
  const { options, condition } = v.branch;
  return [
    h("div", { class: "pane-note" }, "Pick a side: keys t / f, or the option's number"),
    h(
      "div",
      { class: "options" },
      ...options.map((opt, i) => h("button", { type: "button", class: "branch-option", onClick: () => run(`branch ${branchArgument(options, i)}`) }, `${i}: ${opt}`))
    ),
    condition !== null && h("pre", { class: "condition", title: "the branch condition" }, condition)
  ].filter((n) => n !== false);
}
function breakpointList(v, run) {
  if (v.breakpoints.length === 0) return [h("div", { class: "empty" }, "None. Click a line of code, or add one below.")];
  return v.breakpoints.map(
    (b, i) => h("div", { class: "bp" }, h("span", {}, `${i}: ${b}`), h("button", { type: "button", class: "small", title: "delete", onClick: () => run(`delete ${i}`) }, "\u2715"))
  );
}
function warningsPane(v) {
  return v.warnings.map((w) => h("pre", { class: "warning" }, w));
}
function statsRows(s) {
  const c = s.counters;
  return [
    ["opcodes", `${c.opcodes} (${c.replayedOpcodes} replayed going back)`],
    ["commands", `${c.commands} in ${fixed(c.commandSecs, 3)}s`],
    ["solver queries", `${c.queries} in ${fixed(c.querySecs, 3)}s`],
    ["  by kind", `${c.branchQueries} branch \xB7 ${c.solutionQueries} solutions \xB7 ${c.fetchQueries} fetch \xB7 ${c.otherQueries} other`],
    ["branches", `${c.branchesOffered} offered \xB7 ${c.branchesTaken} taken`],
    ["static decisions", `${c.staticDecisions} (${c.staticWrong} wrong \xB7 ${c.staticMissed} missed \xB7 ${c.staticInconclusive} unchecked)`],
    ["breakpoint hits", String(c.breakpointHits)],
    ["snapshots", String(s.snapshotCount)]
  ];
}
function statsPane(s) {
  if (s === null) return [h("div", { class: "empty" }, "\u2026")];
  return [h("table", {}, ...statsRows(s).map(([k, val]) => h("tr", {}, h("th", {}, k), h("td", {}, val))))];
}
function progressPane(p, busy) {
  if (p === null || !p.running) return [h("div", { class: "empty" }, busy ? "Working\u2026" : "Idle.")];
  const solving = p.queries.inFlight.filter((q) => q.solving);
  return [
    h("div", { class: busy ? "progress-line busy" : "progress-line" }, busy ? "Working \xB7 " : "", `${p.queries.done} solver queries done`),
    ...solving.map((q) => h("div", { class: "solving" }, `solving ${q.kind ?? "a query"} for ${fixed(q.secs, 1)}s${q.pc !== void 0 ? ` at pc ${hex(q.pc)}` : ""}`)),
    ...p.hottest.length > 0 ? [h("div", { class: "pane-note" }, "Most solver time:")] : [],
    ...p.hottest.slice(0, 5).map((s) => h("div", { class: "hot" }, `pc ${hex(s.pc)} \xB7 ${fixed(s.solveSecs, 2)}s \xB7 ${s.queries} queries`))
  ];
}
function logPane(log) {
  return log.map((e) => h("pre", { class: `log-${e.kind}` }, e.text));
}

// src/app.ts
function byId(id) {
  const node = document.getElementById(id);
  if (node === null) throw new Error(`the page has no #${id}`);
  return node;
}
var App = class {
  model = initialModel;
  history = [];
  historyPos = 0;
  input = byId("command");
  breakInput = byId("break-input");
  async start() {
    this.input.addEventListener("keydown", (e) => this.onConsoleKey(e));
    this.breakInput.addEventListener("keydown", (e) => {
      if (e.key === "Enter" && this.breakInput.value.trim() !== "") {
        this.run(`break ${this.breakInput.value.trim()}`);
        this.breakInput.value = "";
      }
    });
    document.addEventListener("keydown", (e) => this.onKey(e));
    for (const button of document.querySelectorAll("[data-command]")) {
      button.addEventListener("click", () => this.run(button.dataset["command"] ?? ""));
    }
    try {
      this.dispatch({ type: "view", view: await api.state() });
    } catch (e) {
      this.dispatch({ type: "failed", error: String(e) });
    }
    await this.refreshSide();
  }
  run = (command) => {
    void this.execute(command);
  };
  dispatch(msg) {
    this.model = update(this.model, msg);
    this.draw();
  }
  async execute(command) {
    if (this.model.busy) {
      this.dispatch({ type: "failed", error: "Still working on the previous command." });
      return;
    }
    this.dispatch({ type: "started", command });
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
  async poll() {
    try {
      this.dispatch({ type: "progress", progress: await api.progress() });
    } catch {
    }
  }
  async refreshSide() {
    try {
      const [stats2, progress2] = await Promise.all([api.stats(), api.progress()]);
      this.dispatch({ type: "stats", stats: stats2 });
      this.dispatch({ type: "progress", progress: progress2 });
    } catch (e) {
      this.dispatch({ type: "failed", error: String(e) });
    }
  }
  draw() {
    const m = this.model;
    document.body.classList.toggle("busy", m.busy);
    const v = m.view;
    if (v !== null) {
      render(byId("status"), statusBar(v));
      render(byId("code"), codePane(v, this.run));
      render(byId("source"), sourcePane(v));
      render(byId("stack"), stackPane(v));
      render(byId("memory"), memoryPane(v, this.run));
      render(byId("branch"), branchPane(v, this.run));
      render(byId("breakpoints"), breakpointList(v, this.run));
      render(byId("warnings-list"), warningsPane(v));
      byId("warnings").hidden = v.warnings.length === 0;
      byId("result").textContent = v.result ?? "";
      byId("code").querySelector(".current")?.scrollIntoView({ block: "nearest" });
    }
    render(byId("stats"), statsPane(m.stats));
    render(byId("progress"), progressPane(m.progress, m.busy));
    const log = byId("log");
    render(log, logPane(m.log));
    log.scrollTop = log.scrollHeight;
  }
  onConsoleKey(e) {
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
  onKey(e) {
    const target = e.target;
    const action = keyAction(
      { key: e.key, ctrl: e.ctrlKey || e.metaKey || e.altKey, inInput: target?.tagName === "INPUT" },
      this.model.view?.branch !== null && this.model.view?.branch !== void 0
    );
    if (action === null) return;
    e.preventDefault();
    if ("run" in action) this.run(action.run);
    else if ("focusConsole" in action) this.input.focus();
    else void this.showHelp();
  }
  async showHelp() {
    const help2 = await api.help();
    const keys = [...Object.entries(shortcuts).map(([k, c]) => `${k}   ${c}`), "0-9 pick that branch option", ":   type a command", "?   this help"];
    const dialog = byId("help");
    render(dialog, [
      h("h2", {}, "Keys"),
      h("pre", {}, keys.join("\n")),
      h("h2", {}, "Commands"),
      h("pre", {}, help2.commands.join("\n")),
      h("p", { class: "pane-note" }, "Click anywhere to close.")
    ]);
    dialog.showModal();
  }
};

// src/main.ts
void new App().start();
