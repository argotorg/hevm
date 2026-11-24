import { indentWithTab } from "@codemirror/commands";
import { syntaxHighlighting } from "@codemirror/language";
import { StateEffect, StateField } from "@codemirror/state";
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

  constructor(parent: HTMLElement, doc: string) {
    this.view = new EditorView({
      parent,
      doc,
      extensions: [basicSetup, keymap.of([indentWithTab]), solidity, syntaxHighlighting(classHighlighter), failing, colors],
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
