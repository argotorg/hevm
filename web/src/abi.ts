// Just enough of the Solidity ABI to show counterexamples as calls and their outcomes as values.
import { describeResult } from "./results";

export interface AbiParam {
  name: string;
  type: string;
  components?: AbiParam[];
}

export interface AbiFunction {
  type: "function";
  name: string;
  inputs: AbiParam[];
  outputs: AbiParam[];
}

export function functions(abi: readonly unknown[]): AbiFunction[] {
  return abi.filter((x): x is AbiFunction => (x as { type?: string }).type === "function");
}

function canonical(p: AbiParam): string {
  return p.type.startsWith("tuple") ? `(${(p.components ?? []).map(canonical).join(",")})${p.type.slice(5)}` : p.type;
}

/** e.g. "transfer(address,uint256)" */
export function signature(f: AbiFunction): string {
  return `${f.name}(${f.inputs.map(canonical).join(",")})`;
}

// large numbers read better in hex, where their bit patterns show
function number(v: bigint): string {
  const abs = v < 0n ? -v : v;
  return abs < 1n << 64n ? v.toString() : `${v < 0n ? "-" : ""}0x${abs.toString(16)}`;
}

/** A 32-byte word as a value of a static type, or undefined for any other type */
export function decodeWord(type: string, word: string): string | undefined {
  if (!/^[0-9a-f]{64}$/i.test(word)) return undefined;
  const v = BigInt("0x" + word);
  let m: RegExpExecArray | null;
  if ((m = /^uint(\d*)$/.exec(type))) return number(v);
  if ((m = /^int(\d*)$/.exec(type))) return number(v >= 1n << 255n ? v - (1n << 256n) : v);
  if (type === "bool") return v === 0n ? "false" : v === 1n ? "true" : undefined;
  if (type === "address") return "0x" + word.slice(24);
  if ((m = /^bytes(\d+)$/.exec(type))) return "0x" + word.slice(0, 2 * Number(m[1]));
  return undefined;
}

/** Hex data as values of static types, or undefined unless they all are */
export function decodeValues(types: string[], hex: string): string[] | undefined {
  if (hex.length < 64 * types.length) return undefined;
  const values = types.map((t, i) => decodeWord(t, hex.slice(64 * i, 64 * (i + 1))));
  return values.every((v) => v !== undefined) ? (values as string[]) : undefined;
}

/** Calldata as a call, e.g. "f(1337)", given the functions and their selectors */
export function describeCall(calldata: string, fns: AbiFunction[], selectors: Record<string, string>): string {
  const hex = calldata.replace(/^0x/, "");
  const f = fns.find((f) => selectors[signature(f)] === hex.slice(0, 8));
  if (!f) return calldata || "0x (empty calldata)";
  const args = decodeValues(f.inputs.map((p) => p.type), hex.slice(8));
  return `${f.name}(${args ? args.join(", ") : hex.length > 8 ? "0x" + hex.slice(8) : ""})`;
}

/** What one program did on a counterexample, from hevm's replay of it, e.g. "returns 2674" */
export function describeOutcome(replay: string, outputs?: AbiParam[]): string {
  const [result, ...rest] = replay.split(", ");
  const extra = rest.length ? ` (${rest.join(", ")})` : "";
  let m: RegExpExecArray | null;
  if ((m = /^Return 0x([0-9a-f]*)$/.exec(result!))) {
    const data = m[1]!;
    if (!data) return "returns nothing" + extra;
    const values = outputs && decodeValues(outputs.map((p) => p.type), data);
    return `returns ${values && data.length === 64 * outputs!.length ? values.join(", ") : "0x" + data}${extra}`;
  }
  if ((m = /^Revert 0x([0-9a-f]*)/.exec(result!))) return `reverts: ${describeResult(`Revert: 0x${m[1]}`)}`;
  return `fails: ${replay}`;
}
