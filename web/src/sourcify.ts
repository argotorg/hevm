// Looks up verified contracts on Sourcify (https://docs.sourcify.dev), one at a time, as its
// fair-use rules ask: only the fields needed, and no lookup twice.

export interface AbiParam {
  name: string;
  type: string;
  components?: AbiParam[];
}

export interface VerifiedContract {
  chainId: string;
  address: string;
  /** the contract, and the file it is in */
  name: string;
  path: string;
  /** solc's long version, e.g. "0.7.6+commit.7338295f" */
  version: string;
  /** solc's settings it was compiled with */
  settings: Record<string, unknown>;
  sources: Record<string, string>;
  constructorInputs: AbiParam[];
  match: string;
  /** the contracts behind it, if it is a proxy */
  implementations: { address: string; name?: string }[];
  /** the code it was deployed with: its runtime code on chain, and its creation code, the
   * constructor's, as Sourcify compiled it */
  deployed?: { runtime: Code; creation?: Code };
}

/** Code as hex, and the bytes that differ from a compilation of the same sources: the
 * immutables, set at deployment, and solc's metadata, which covers all files compiled */
export interface Code {
  code: string;
  ignore: { start: number; length: number }[];
}

function sameCode(compiled: string, expected: Code): boolean {
  const ours = compiled.replace(/^0x/, "").toLowerCase();
  if (ours.length !== expected.code.length) return false;
  const blank = (code: string) =>
    expected.ignore.reduce((c, r) => c.slice(0, 2 * r.start) + "00".repeat(r.length) + c.slice(2 * (r.start + r.length)), code);
  return blank(ours) === blank(expected.code);
}

/** Whether compiled code is what the contract was deployed with, but for the bytes that may differ */
export function sameAsDeployed(compiled: { runtime: string; creation: string }, deployed: NonNullable<VerifiedContract["deployed"]>): boolean {
  return sameCode(compiled.runtime, deployed.runtime) && (!deployed.creation || sameCode(compiled.creation, deployed.creation));
}

export const chains: { id: string; name: string }[] = [
  { id: "1", name: "Ethereum" },
  { id: "11155111", name: "Sepolia" },
  { id: "17000", name: "Holesky" },
  { id: "10", name: "OP Mainnet" },
  { id: "42161", name: "Arbitrum One" },
  { id: "8453", name: "Base" },
  { id: "137", name: "Polygon" },
  { id: "56", name: "BNB Smart Chain" },
  { id: "100", name: "Gnosis" },
  { id: "43114", name: "Avalanche C-Chain" },
];

/** A contract's page on Sourcify */
export const repoUrl = (chainId: string, address: string) => `https://repo.sourcify.dev/${chainId}/${address}`;

/** An address, or a link to a contract on Sourcify, which names its chain too */
export function parseTarget(text: string): { chainId?: string; address: string } | undefined {
  const t = text.trim();
  const link = /sourcify\.dev\/(?:[^/]+\/)*?(\d+)\/(0x[0-9a-fA-F]{40})\b/.exec(t);
  if (link) return { chainId: link[1]!, address: link[2]! };
  return /^0x[0-9a-fA-F]{40}$/.test(t) ? { address: t } : undefined;
}

interface Response {
  match?: string;
  compilation?: {
    language: string;
    compilerVersion: string;
    compilerSettings: Record<string, unknown>;
    fullyQualifiedName: string;
  };
  sources?: Record<string, { content: string }>;
  abi?: { type: string; inputs?: AbiParam[] }[];
  proxyResolution?: { isProxy?: boolean; implementations?: { address: string; name?: string }[] } | null;
  runtimeBytecode?: {
    onchainBytecode?: string;
    immutableReferences?: Record<string, { start: number; length: number }[]> | null;
    cborAuxdata?: Auxdata;
  };
  creationBytecode?: { recompiledBytecode?: string; cborAuxdata?: Auxdata };
}

type Auxdata = Record<string, { offset: number; value: string }> | null;

const auxdata = (a: Auxdata | undefined) => Object.values(a ?? {}).map((x) => ({ start: x.offset, length: (x.value.length - 2) / 2 }));
const hex = (code: string) => code.replace(/^0x/, "").toLowerCase();

/** How a Sourcify answer becomes a contract to test */
export function readVerified(chainId: string, address: string, r: Response): VerifiedContract {
  const c = r.compilation;
  if (!c || !r.sources) throw new Error("Sourcify's answer lacks the compilation or the sources");
  if (c.language !== "Solidity") throw new Error(`${c.language} contracts are not supported yet, only Solidity`);
  const split = c.fullyQualifiedName.lastIndexOf(":");
  // the input's own settings, not those of the metadata, and outputs are hevm's choice
  const { compilationTarget: _t, outputSelection: _o, ...settings } = c.compilerSettings;
  return {
    chainId,
    address,
    name: c.fullyQualifiedName.slice(split + 1),
    path: c.fullyQualifiedName.slice(0, split),
    version: c.compilerVersion.replace(/^v/, ""),
    settings,
    sources: Object.fromEntries(Object.entries(r.sources).map(([path, s]) => [path, s.content])),
    constructorInputs: r.abi?.find((x) => x.type === "constructor")?.inputs ?? [],
    match: r.match ?? "match",
    implementations: r.proxyResolution?.isProxy ? (r.proxyResolution.implementations ?? []) : [],
    ...(r.runtimeBytecode?.onchainBytecode && {
      deployed: {
        runtime: {
          code: hex(r.runtimeBytecode.onchainBytecode),
          ignore: [...Object.values(r.runtimeBytecode.immutableReferences ?? {}).flat(), ...auxdata(r.runtimeBytecode.cborAuxdata)],
        },
        ...(r.creationBytecode?.recompiledBytecode && {
          creation: { code: hex(r.creationBytecode.recompiledBytecode), ignore: auxdata(r.creationBytecode.cborAuxdata) },
        }),
      },
    }),
  };
}

const looked = new Map<string, Promise<VerifiedContract>>();

export function fetchVerified(chainId: string, address: string, get: typeof fetch = fetch): Promise<VerifiedContract> {
  const key = `${chainId}:${address.toLowerCase()}`;
  let found = looked.get(key);
  if (!found) {
    found = (async () => {
      const fields = "sources,compilation,abi,proxyResolution,"
        + "runtimeBytecode.onchainBytecode,runtimeBytecode.immutableReferences,runtimeBytecode.cborAuxdata,"
        + "creationBytecode.recompiledBytecode,creationBytecode.cborAuxdata";
      const url = `https://sourcify.dev/server/v2/contract/${chainId}/${address}?fields=${fields}`;
      const res = await get(url);
      if (res.status === 404) throw new Error(`${address} is not verified on Sourcify for chain ${chainId}`);
      if (res.status === 429) throw new Error("Sourcify asks to slow down: try again in a minute");
      if (!res.ok) throw new Error(`Sourcify answered ${res.status}`);
      return readVerified(chainId, address, (await res.json()) as Response);
    })();
    looked.set(key, found);
    found.catch(() => looked.delete(key));
  }
  return found;
}
