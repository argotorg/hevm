// What a tab holds, as the hash of a link: examples by name, anything else deflated.
import type { EqMode } from "./equivalence";
import type { Request } from "./hevm";

export type Shared =
  | { tab: "sol"; example: string }
  | { tab: "sol"; source: string }
  | { tab: "eq"; example: string }
  | { tab: "eq"; source: string; mode: EqMode; a: string; b: string }
  | { tab: "bytecode"; request: Request };

async function pipe(bytes: Uint8Array<ArrayBuffer>, stream: CompressionStream | DecompressionStream): Promise<Uint8Array<ArrayBuffer>> {
  const out = new Blob([bytes]).stream().pipeThrough(stream);
  return new Uint8Array(await new Response(out).arrayBuffer());
}

function base64url(bytes: Uint8Array): string {
  let s = "";
  for (const b of bytes) s += String.fromCharCode(b);
  return btoa(s).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

function unbase64url(text: string): Uint8Array<ArrayBuffer> {
  const s = atob(text.replace(/-/g, "+").replace(/_/g, "/"));
  return Uint8Array.from(s, (c) => c.charCodeAt(0));
}

async function pack(value: unknown): Promise<string> {
  return base64url(await pipe(new TextEncoder().encode(JSON.stringify(value)), new CompressionStream("deflate-raw")));
}

async function unpack(text: string): Promise<unknown> {
  return JSON.parse(new TextDecoder().decode(await pipe(unbase64url(text), new DecompressionStream("deflate-raw"))));
}

/** The hash of a link to it, without the "#" */
export async function encodeShare(s: Shared): Promise<string> {
  const params = new URLSearchParams({ tab: s.tab });
  if ("example" in s) params.set("example", s.example);
  else if (s.tab === "bytecode") params.set("s", await pack(s.request));
  else params.set("s", await pack(s.tab === "sol" ? { source: s.source } : { source: s.source, mode: s.mode, a: s.a, b: s.b }));
  return params.toString();
}

/** What a link's hash holds, or undefined if it holds nothing this page knows */
export async function decodeShare(hash: string): Promise<Shared | undefined> {
  const params = new URLSearchParams(hash.replace(/^#/, ""));
  const tab = params.get("tab");
  const example = params.get("example");
  const packed = params.get("s");
  try {
    if (tab === "sol" && example) return { tab, example };
    if (tab === "eq" && example) return { tab, example };
    if (!packed) return undefined;
    const v = (await unpack(packed)) as Record<string, string>;
    if (tab === "sol" && typeof v.source === "string") return { tab, source: v.source };
    if (tab === "eq" && typeof v.source === "string" && ["contracts", "optimizer", "via-ir"].includes(v.mode!)) {
      return { tab, source: v.source, mode: v.mode as EqMode, a: String(v.a ?? ""), b: String(v.b ?? "") };
    }
    if (tab === "bytecode" && (v.mode === "exec" || v.mode === "symbolic") && typeof v.code === "string") {
      return { tab, request: v as unknown as Request };
    }
  } catch {
    // a link cut short, or not ours
  }
  return undefined;
}
