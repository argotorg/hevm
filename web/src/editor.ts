import { indentWithTab } from "@codemirror/commands";
import { syntaxHighlighting } from "@codemirror/language";
import { EditorState, StateEffect, StateField, type Extension } from "@codemirror/state";
import { Decoration, keymap, type DecorationSet } from "@codemirror/view";
import { classHighlighter } from "@lezer/highlight";
import { solidity } from "@replit/codemirror-lang-solidity";
import { EditorView, basicSetup } from "codemirror";

const setFailing = StateEffect.define<number[]>();

// CodeMirror's defaults are for light pages: a fixed light purple selection, unreadable
// under light text, and a thin black cursor, invisible on a dark background
const colors = EditorView.theme({
  "&.cm-focused > .cm-scroller > .cm-selectionLayer .cm-selectionBackground, .cm-selectionBackground, .cm-content ::selection":
    { backgroundColor: "var(--selection)" },
  ".cm-cursor, .cm-dropCursor": { borderLeft: "2px solid var(--accent)" },
});

// lines where a counterexample fails, until the source changes
const failing = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update(deco, tr) {
    deco = tr.docChanged ? Decoration.none : deco;
    for (const e of tr.effects) {
      if (!e.is(setFailing)) continue;
      const lines = [...new Set(e.value)].filter((l) => l >= 1 && l <= tr.state.doc.lines).sort((a, b) => a - b);
      deco = Decoration.set(lines.map((l) => Decoration.line({ class: "cm-failing" }).range(tr.state.doc.line(l).from)));
    }
    return deco;
  },
  provide: (f) => EditorView.decorations.from(f),
});

export class SolidityEditor {
  readonly view: EditorView;

  constructor(parent: HTMLElement, doc: string, onChange?: (text: string) => void) {
    const changes = EditorView.updateListener.of((u) => {
      if (u.docChanged) onChange?.(u.state.doc.toString());
    });
    this.view = new EditorView({
      parent,
      doc,
      extensions: [basicSetup, keymap.of([indentWithTab]), solidity, syntaxHighlighting(classHighlighter), failing, colors, changes],
    });
  }

  get value(): string {
    return this.view.state.doc.toString();
  }

  set value(text: string) {
    this.view.dispatch({ changes: { from: 0, to: this.view.state.doc.length, insert: text } });
  }

  markFailing(lines: number[]) {
    this.view.dispatch({ effects: setFailing.of(lines) });
  }

  selectLine(n: number) {
    const line = this.view.state.doc.line(Math.min(Math.max(1, n), this.view.state.doc.lines));
    this.view.dispatch({ selection: { anchor: line.from, head: line.to }, scrollIntoView: true });
    this.view.focus();
  }
}

/** One editor for the files of a project, each with its own undo history */
export class ProjectEditor {
  readonly view: EditorView;
  private readonly extensions: Extension[];
  private readonly states = new Map<string, EditorState>();
  private failingLines = new Map<string, number[]>();
  current = "";

  /** onChange gets the path of a file that was edited, or opened */
  constructor(parent: HTMLElement, private readonly onChange: (path: string) => void) {
    const changes = EditorView.updateListener.of((u) => {
      if (u.docChanged) this.onChange(this.current);
    });
    this.extensions = [basicSetup, keymap.of([indentWithTab]), solidity, syntaxHighlighting(classHighlighter), failing, colors, changes];
    this.view = new EditorView({ parent, state: EditorState.create({ extensions: this.extensions }) });
  }

  /** Replaces all the files, and opens one */
  load(files: Record<string, string>, open: string) {
    this.states.clear();
    this.failingLines.clear();
    for (const [path, text] of Object.entries(files)) this.states.set(path, EditorState.create({ doc: text, extensions: this.extensions }));
    this.current = "";
    this.open(open);
  }

  paths(): string[] {
    return [...this.states.keys()];
  }

  has(path: string): boolean {
    return this.states.has(path);
  }

  text(path: string): string | undefined {
    return path === this.current ? this.view.state.doc.toString() : this.states.get(path)?.doc.toString();
  }

  get value(): string {
    return this.view.state.doc.toString();
  }

  open(path: string) {
    if (!this.states.has(path)) return;
    if (this.current) this.states.set(this.current, this.view.state);
    this.current = path;
    this.view.setState(this.states.get(path)!);
    this.view.dispatch({ effects: setFailing.of(this.failingLines.get(path) ?? []) });
    this.onChange(path);
  }

  set(path: string, text: string) {
    const state = EditorState.create({ doc: text, extensions: this.extensions });
    this.states.set(path, state);
    if (path === this.current) this.view.setState(state);
  }

  remove(path: string) {
    this.states.delete(path);
    this.failingLines.delete(path);
    if (path === this.current) {
      this.current = "";
      const next = this.paths()[0];
      if (next) this.open(next);
    }
  }

  /** Marks lines where a counterexample fails, per file, until that file changes */
  markFailing(byFile: Map<string, number[]>) {
    this.failingLines = byFile;
    this.view.dispatch({ effects: setFailing.of(byFile.get(this.current) ?? []) });
  }

  selectLine(path: string, n: number) {
    this.open(path);
    const doc = this.view.state.doc;
    const line = doc.line(Math.min(Math.max(1, n), doc.lines));
    this.view.dispatch({ selection: { anchor: line.from, head: line.to }, scrollIntoView: true });
    this.view.focus();
  }
}
