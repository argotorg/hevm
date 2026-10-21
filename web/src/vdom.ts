// A minimal virtual DOM: views build these plain objects, so they can be tested
// without a browser, and only `render` touches the real DOM.

export interface VNode {
  tag: string;
  props: Props;
  children: VNode[];
}

export interface Props {
  class?: string;
  title?: string;
  onClick?: () => void;
  [attr: string]: string | (() => void) | undefined;
}

// A text node is a VNode with tag "#text" and the text in props.text
export type Child = VNode | string | number | null | undefined | false;

export function h(tag: string, props: Props = {}, ...children: Child[]): VNode {
  const kids: VNode[] = [];
  for (const c of children) {
    if (c === null || c === undefined || c === false) continue;
    kids.push(typeof c === "object" ? c : text(String(c)));
  }
  return { tag, props, children: kids };
}

export function text(s: string): VNode {
  return { tag: "#text", props: { text: s }, children: [] };
}

// All the text in a tree, e.g. for tests
export function textOf(node: VNode): string {
  if (node.tag === "#text") return String(node.props["text"] ?? "");
  return node.children.map(textOf).join("");
}

// Every node in a tree that satisfies the predicate
export function findAll(node: VNode, pred: (n: VNode) => boolean): VNode[] {
  const found = pred(node) ? [node] : [];
  return found.concat(...node.children.map((c) => findAll(c, pred)));
}

export function hasClass(node: VNode, cls: string): boolean {
  return (node.props.class ?? "").split(" ").includes(cls);
}

function toDom(node: VNode): Node {
  if (node.tag === "#text") return document.createTextNode(String(node.props["text"] ?? ""));
  const el = document.createElement(node.tag);
  for (const [k, v] of Object.entries(node.props)) {
    if (v === undefined) continue;
    if (k === "onClick" && typeof v === "function") el.addEventListener("click", v);
    else if (typeof v === "string") el.setAttribute(k, v);
  }
  for (const c of node.children) el.append(toDom(c));
  return el;
}

export function render(container: HTMLElement, nodes: VNode[]): void {
  container.replaceChildren(...nodes.map(toDom));
}
