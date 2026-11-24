// The Solidity tab's project: its files, the solc version and settings to compile them with,
// and where they came from: an example, a link, or a verified contract on Sourcify.
import { $, el } from "./dom";
import { ProjectEditor } from "./editor";
import { importClosure } from "./imports";
import { bundledSolc, type CompileSettings, type Source } from "./solc";
import { solcReleases } from "./solcReleases";
import { chains, fetchVerified, parseTarget, repoUrl, type VerifiedContract } from "./sourcify";
import { sourcifyExample, sourcifyExamples } from "./sourcifyExamples";
import { starterPath, starterTest } from "./starter";

export interface SolProject {
  /** every file as it came: for a verified contract, all sources of its compilation */
  files: Record<string, string>;
  /** where compiling starts: the contract under test, and the tests. Their imports come along */
  roots: string[];
  /** solc's long version, or the built-in one */
  version?: string;
  settings?: Record<string, unknown>;
  verified?: VerifiedContract;
  /** whether the last compile of the verified contract gave the code deployed */
  deployedCheck?: { same: boolean; text: string };
}

export const examplePath = "src/Main.sol";

const shortVersion = (v: string) => v.split("+")[0]!;

export class Workspace {
  project: SolProject = { files: {}, roots: [] };
  readonly editor: ProjectEditor;
  private readonly panel = $<HTMLElement>("files");
  private readonly fileSelect = $<HTMLSelectElement>("file-select");
  private readonly version = $<HTMLSelectElement>("sol-version");
  private readonly origin = $<HTMLElement>("sol-origin");
  private refresh = 0;

  constructor(private readonly onEdit: () => void) {
    this.editor = new ProjectEditor($("source"), () => {
      cancelAnimationFrame(this.refresh);
      this.refresh = requestAnimationFrame(() => this.render());
      this.onEdit();
    });
    this.version.add(new Option(`${bundledSolc} (built in)`, ""));
    for (const v of solcReleases) if (shortVersion(v) !== bundledSolc) this.version.add(new Option(shortVersion(v), v));
    this.version.addEventListener("change", () => (this.project.version = this.version.value || undefined));
    this.fileSelect.addEventListener("change", () => this.editor.open(this.fileSelect.value));
    $("new-file").addEventListener("click", () => this.newFile());
  }

  private setVersion(version?: string) {
    if (version && ![...this.version.options].some((o) => o.value === version)) {
      this.version.add(new Option(shortVersion(version), version), 1);
    }
    this.version.value = version && shortVersion(version) !== bundledSolc ? version : "";
    this.project.version = this.version.value || undefined;
  }

  private show(project: SolProject, open: string) {
    this.project = project;
    this.editor.load(project.files, open);
    this.setVersion(project.version);
    this.showOrigin();
    this.render();
  }

  /** No files: nothing loaded yet */
  clear() {
    this.show({ files: {}, roots: [] }, "");
  }

  empty(): boolean {
    return this.editor.paths().length === 0;
  }

  snapshot() {
    return { project: this.project, editor: this.editor.snapshot() };
  }

  restore(s: ReturnType<Workspace["snapshot"]>) {
    this.project = s.project;
    this.editor.restore(s.editor);
    this.setVersion(s.project.version);
    this.showOrigin();
    this.render();
  }

  loadExample(source: string) {
    this.show({ files: { [examplePath]: source }, roots: [examplePath] }, examplePath);
  }

  /** Files from a link: the ones it holds, on top of a verified contract's if it names one */
  loadFiles(files: Record<string, string>, version?: string, verified?: VerifiedContract) {
    const base = verified ? this.verifiedProject(verified, false) : { files: {}, roots: [] };
    const added = Object.keys(files).filter((p) => !(p in base.files));
    const project: SolProject = {
      ...base,
      files: { ...base.files, ...Object.fromEntries(added.map((p) => [p, files[p]!])) },
      roots: [...base.roots, ...added],
      version: version ?? base.version,
    };
    this.show(project, added[0] ?? project.roots[0]!);
    for (const [path, text] of Object.entries(files)) if (!added.includes(path)) this.editor.set(path, text);
    this.render();
  }

  private verifiedProject(c: VerifiedContract, withStarter: boolean): SolProject {
    const files = { ...c.sources };
    const roots = [c.path];
    // an example's own tests, or a starter test
    const example = sourcifyExample(c.chainId, c.address);
    const path = example?.testPath ?? starterPath(c);
    if (withStarter && !(path in files)) {
      files[path] = example?.test ?? starterTest(c);
      roots.push(path);
    }
    return { files, roots, version: c.version, settings: c.settings, verified: c };
  }

  loadVerified(c: VerifiedContract) {
    const project = this.verifiedProject(c, true);
    this.show(project, project.roots.at(-1)!);
  }

  /** The files there are now, as edited */
  current(): Record<string, string> {
    return Object.fromEntries(this.editor.paths().map((p) => [p, this.editor.text(p)!]));
  }

  private remappings(): string[] {
    const r = this.project.settings?.remappings;
    return Array.isArray(r) ? r.map(String) : [];
  }

  /** The files compiled: the roots, the files they import, and those the user added */
  visible(): string[] {
    const files = this.current();
    const roots = this.project.roots.filter((p) => p in files);
    const added = Object.keys(files).filter((p) => !(p in this.project.files));
    return importClosure(files, [...roots, ...added], this.remappings()).filter((p) => p !== "hevm/Test.sol" || p in files);
  }

  sources(): Source[] {
    return this.visible().map((path) => ({ path, content: this.editor.text(path)! }));
  }

  settings(): CompileSettings | undefined {
    return this.project.settings ? { solc: this.project.settings } : undefined;
  }

  /** The verified contract's own files that were edited, among those compiled */
  editedSources(): string[] {
    const v = this.project.verified;
    return v ? this.visible().filter((p) => p in v.sources && this.editor.text(p) !== v.sources[p]) : [];
  }

  /** Files added or changed, compared with the project as it came */
  changes(): Record<string, string> {
    return Object.fromEntries(Object.entries(this.current()).filter(([p, text]) => this.project.files[p] !== text));
  }

  /** Whether the project is one file, as an example is */
  single(): boolean {
    return this.editor.paths().length === 1 && !this.project.verified;
  }

  private newFile() {
    const name = this.project.verified?.name ?? "My";
    const path = prompt("The new file's path, e.g. a test:", `test/${name}2.t.sol`)?.trim();
    if (!path) return;
    if (!path.endsWith(".sol")) return alert("A Solidity file's name ends in .sol");
    if (this.editor.has(path)) return alert(`There is a ${path} already`);
    const contract = (path.split("/").pop()!.replace(/\.t?\.?sol$/i, "").replace(/\W/g, "") || "My") + "Test";
    const imports = this.project.verified
      ? `import {${this.project.verified.name}} from "${this.project.verified.path}";\n`
      : "";
    this.editor.set(path, `// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.4.17;

import {Test} from "hevm/Test.sol";
${imports}
contract ${/^\d/.test(contract) ? `T${contract}` : contract} is Test {
    function prove_something(uint256 x) public {
        assert(x == x);
    }
}
`);
    this.editor.open(path);
    this.render();
  }

  private removeFile(path: string) {
    if (!confirm(`Delete ${path}?`)) return;
    this.editor.remove(path);
    this.project.roots = this.project.roots.filter((p) => p !== path);
    this.render();
  }

  showOrigin() {
    const c = this.project.verified;
    this.origin.hidden = !c;
    if (!c) return this.origin.replaceChildren();
    const link = el("a", undefined, `${c.address.slice(0, 8)}…${c.address.slice(-6)}`);
    link.href = repoUrl(c.chainId, c.address);
    link.target = "_blank";
    link.rel = "noopener";
    const chain = chains.find((x) => x.id === c.chainId)?.name ?? `chain ${c.chainId}`;
    const optimizer = c.settings.optimizer as { enabled?: boolean; runs?: number } | undefined;
    const parts: (string | Node)[] = [
      el("b", undefined, c.name), ` at `, link, ` on ${chain}, verified on Sourcify (${c.match.replace("_", " ")}). `,
      `Compiled with solc ${shortVersion(c.version)}${optimizer?.enabled ? `, optimizer on (${optimizer.runs} runs)` : ""}. `,
      `Your tests go next to it, in test/; hevm runs them against a fresh deployment, not the chain's state.`,
    ];
    const libraries = c.settings.libraries as Record<string, unknown> | undefined;
    if (libraries && Object.values(libraries).some((l) => l && Object.keys(l as object).length)) {
      parts.push(" It links libraries deployed at fixed addresses, which are empty here: calls to them fail.");
    }
    this.origin.replaceChildren(...parts);
    const check = this.project.deployedCheck;
    if (check) this.origin.append(el("p", `deployed ${check.same ? "same" : "differs"}`, check.text));
    if (c.implementations.length) {
      const impl = c.implementations[0]!;
      const load = el("button", "secondary", `Load ${impl.name ?? "the implementation"} instead`);
      load.type = "button";
      load.addEventListener("click", () => void this.onLoadRequest?.(c.chainId, impl.address));
      const p = el("p", undefined, `This is a proxy: its logic is in ${impl.name ?? "a contract"} at ${impl.address}. `);
      p.append(load);
      this.origin.append(p);
    }
  }

  /** Called to load another verified contract, e.g. a proxy's implementation */
  onLoadRequest?: (chainId: string, address: string) => Promise<void>;

  render() {
    const visible = this.visible();
    const current = this.editor.current;
    const many = visible.length > 1 || !!this.project.verified;
    $<HTMLFormElement>("sol-form").dataset.empty = String(this.empty());
    this.panel.hidden = !many;
    this.fileSelect.hidden = !many;
    const user = (p: string) => !(p in this.project.files) || (this.project.verified ? !(p in this.project.verified.sources) : false);
    const modified = (p: string) => p in this.project.files && this.editor.text(p) !== this.project.files[p];
    // the user's files first, then the contract's, by folder
    const sorted = [...visible].sort((a, b) => Number(user(b)) - Number(user(a)) || a.localeCompare(b));
    const list = el("ul");
    let dir: string | undefined;
    for (const path of sorted) {
      const d = path.includes("/") ? path.slice(0, path.lastIndexOf("/") + 1) : "";
      if (d !== dir) {
        dir = d;
        if (d) list.append(el("li", "dir", d));
      }
      const item = el("li", ["file", path === current && "current", modified(path) && "modified", user(path) && "user"].filter(Boolean).join(" "));
      const open = el("button", undefined, path.slice(d.length));
      open.type = "button";
      open.title = path;
      open.addEventListener("click", () => this.editor.open(path));
      item.append(open);
      if (user(path) && this.editor.paths().length > 1) {
        const del = el("button", "delete", "×");
        del.type = "button";
        del.title = `Delete ${path}`;
        del.addEventListener("click", () => this.removeFile(path));
        item.append(del);
      }
      list.append(item);
    }
    const head = el("p", "files-head", `${visible.length} file${visible.length === 1 ? "" : "s"}`);
    if (this.project.verified) {
      head.title = `${Object.keys(this.project.verified.sources).length} in the verified compilation; these are the ones compiled`;
    }
    this.panel.replaceChildren(head, list);
    this.fileSelect.replaceChildren(...sorted.map((p) => new Option(p + (modified(p) ? " •" : ""), p)));
    this.fileSelect.value = current;
  }
}

/** The form that loads a verified contract from Sourcify */
export function setupSourcify(workspace: Workspace, onLoaded: () => void) {
  const chain = $<HTMLSelectElement>("sf-chain");
  const otherField = $<HTMLElement>("sf-chain-other");
  const otherId = $<HTMLInputElement>("sf-chain-id");
  const address = $<HTMLInputElement>("sf-address");
  const loadButton = $<HTMLButtonElement>("sf-load");
  const message = $<HTMLElement>("sf-message");
  for (const c of chains) chain.add(new Option(`${c.name} (${c.id})`, c.id));
  chain.add(new Option("Other chain…", "other"));
  chain.addEventListener("change", () => (otherField.hidden = chain.value !== "other"));
  // an example is filled in, for one click to load it with its tests
  const examples = $<HTMLElement>("sf-examples");
  const fill = (ex: (typeof sourcifyExamples)[number]) => {
    chain.value = ex.chainId;
    otherField.hidden = true;
    address.value = ex.address;
  };
  fill(sourcifyExamples[0]!);
  examples.append("Filled in: ");
  sourcifyExamples.forEach((ex, i) => {
    const b = el("button", "link", ex.name);
    b.type = "button";
    b.addEventListener("click", () => fill(ex));
    examples.append(...(i ? [", ", b] : [b]));
  });
  examples.append(", on Ethereum, with tests of it to prove. Or put in any verified contract.");

  const load = async (chainId: string, addr: string) => {
    loadButton.disabled = true;
    message.textContent = `Looking up ${addr} on Sourcify…`;
    try {
      workspace.loadVerified(await fetchVerified(chainId, addr));
      message.textContent = "";
      onLoaded();
    } catch (err) {
      message.textContent = (err as Error).message;
    } finally {
      loadButton.disabled = false;
    }
  };
  workspace.onLoadRequest = load;

  const submit = () => {
    const target = parseTarget(address.value);
    if (!target) {
      message.textContent = "That is not an address (0x and 40 hex digits), nor a link to a contract on Sourcify.";
      return;
    }
    if (target.chainId) {
      const known = chains.some((c) => c.id === target.chainId);
      chain.value = known ? target.chainId : "other";
      otherField.hidden = known;
      if (!known) otherId.value = target.chainId;
    }
    const chainId = chain.value === "other" ? otherId.value.trim() : chain.value;
    if (!/^\d+$/.test(chainId)) {
      message.textContent = "Which chain? Its ID is a number, e.g. 1 for Ethereum.";
      return;
    }
    void load(chainId, target.address);
  };
  loadButton.addEventListener("click", submit);
  address.addEventListener("keydown", (e) => {
    if (e.key === "Enter") {
      e.preventDefault();
      submit();
    }
  });
  return { load };
}
