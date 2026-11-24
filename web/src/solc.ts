// Compiles with soljson (solc's emscripten build), of any version from 0.4.11 on, and lays
// the output out as forge's out/ directory, which `hevm test` reads.

export interface Soljson {
  cwrap(name: string, ret: string | null, args: string[]): (...args: unknown[]) => unknown;
  [exported: `_${string}`]: unknown;
}

export interface Source {
  path: string;
  content: string;
}

export interface CompileError {
  severity: string;
  message: string;
  formatted: string;
  file?: string;
  start?: number;
  end?: number;
}

/** hevm only tests contracts with an IS_TEST() marker, which forge-std's Test usually provides */
export const testBase: Source = {
  path: "hevm/Test.sol",
  content: `// SPDX-License-Identifier: MIT
pragma solidity >=0.4.17;

// Contracts inheriting this are tests: hevm proves their prove_ functions, and checks
// their invariant_ functions after every sequence of calls to the contracts setUp() deploys
contract Test {
    bool public IS_TEST = true;

    address[] private _targetContracts;
    address[] private _targetSenders;

    // as forge-std's StdInvariant: call only these contracts, only from these addresses
    function targetContract(address target) internal {
        _targetContracts.push(target);
    }

    function targetSender(address sender) internal {
        _targetSenders.push(sender);
    }

    function targetContracts() public view returns (address[] memory) {
        return _targetContracts;
    }

    function targetSenders() public view returns (address[] memory) {
        return _targetSenders;
    }
}
`,
};

interface StandardOutput {
  errors?: {
    severity: string;
    message: string;
    formattedMessage: string;
    sourceLocation?: { file: string; start: number; end: number };
  }[];
  sources?: Record<string, { id: number; ast: unknown }>;
  contracts?: Record<string, Record<string, ContractOutput>>;
}

interface Bytecode {
  object: string;
  sourceMap: string;
  immutableReferences?: unknown;
}

interface ContractOutput {
  abi: unknown[];
  storageLayout?: unknown;
  evm: { bytecode: Bytecode; deployedBytecode: Bytecode; methodIdentifiers?: Record<string, string> };
}

/** Runs a soljson script, a classic script that defines Module. Node's globals are hidden from
 * it, so that under Node, too, it takes the path it takes in a browser's worker. */
export function evalSoljson(text: string): Soljson {
  const run = new Function("process", "require", "module", "exports", "__dirname", "__filename", "print", "printErr", "console",
    `${text}\nreturn Module;`);
  // before about 0.5, outside a browser it takes the path of a JavaScript shell: it prints with print(), and
  // points console.log at it, so it gets a console of its own
  const quiet = () => {};
  return run(undefined, undefined, undefined, undefined, undefined, undefined, quiet, quiet, Object.create(console)) as Soljson;
}

// 25 MB each: kept in the browser's cache, which pages served over http:// do not have
export async function fetchSoljson(url: string): Promise<string> {
  const cache = typeof caches === "undefined" ? undefined : await caches.open("soljson").catch(() => undefined);
  const hit = await cache?.match(url);
  if (hit) return hit.text();
  const res = await fetch(url);
  if (!res.ok) throw new Error(`could not download ${url}: ${res.status}`);
  await cache?.put(url, res.clone()).catch(() => {});
  return res.text();
}

/** The version of the soljson the site comes with */
export const bundledSolc = "0.8.39";

/** Where solc's builds of a version, e.g. "0.7.6+commit.7338295f", are */
export const solcUrl = (version: string) => `https://binaries.soliditylang.org/bin/soljson-v${version}.js`;

export function solcVersion(solc: Soljson): string {
  const name = solc._solidity_version ? "solidity_version" : "version";
  return solc.cwrap(name, "string", [])() as string;
}

export interface CompileSettings {
  optimize?: boolean;
  viaIR?: boolean;
  /** solc's own settings, e.g. a verified contract's: optimizer, evmVersion, remappings */
  solc?: Record<string, unknown>;
}

function solcSettings(settings: CompileSettings): Record<string, unknown> {
  const own = settings.solc ?? {};
  return {
    ...own,
    ...(settings.optimize !== undefined || !own.optimizer ? { optimizer: { enabled: settings.optimize ?? false, runs: 200 } } : {}),
    ...(settings.viaIR !== undefined && { viaIR: settings.viaIR }),
  };
}

export function compileStandard(solc: Soljson, sources: Source[], settings: CompileSettings = {}): StandardOutput {
  const input = JSON.stringify({
    language: "Solidity",
    sources: Object.fromEntries(sources.map((s) => [s.path, { content: s.content }])),
    settings: {
      ...solcSettings(settings),
      outputSelection: {
        "*": {
          "*": [
            "abi",
            "storageLayout",
            "evm.bytecode.object",
            "evm.bytecode.sourceMap",
            "evm.deployedBytecode.object",
            "evm.deployedBytecode.sourceMap",
            "evm.deployedBytecode.immutableReferences",
            "evm.methodIdentifiers",
          ],
          "": ["ast"],
        },
      },
    },
  });
  // as solc-js does it: solidity_compile has taken a callback context since 0.6
  let out: string;
  if (solc._solidity_compile) {
    const [major, minor] = solcVersion(solc).split(".").map(Number);
    const since6 = major! > 0 || minor! >= 6;
    const compile = solc.cwrap("solidity_compile", "string", since6 ? ["string", "number", "number"] : ["string", "number"]);
    out = (since6 ? compile(input, 0, 0) : compile(input, 0)) as string;
  } else if (solc._compileStandard) {
    out = solc.cwrap("compileStandard", "string", ["string", "number"])(input, 0) as string;
  } else {
    throw new Error(`solc ${solcVersion(solc)} has no standard JSON interface: hevm needs 0.4.11 or newer`);
  }
  if (solc._solidity_reset) solc.cwrap("solidity_reset", null, [])();
  return JSON.parse(out) as StandardOutput;
}

export interface Project {
  errors: CompileError[];
  /** paths under the project root and their contents, or null for an empty directory */
  files: Record<string, string | null>;
}

/** Where a contract's artifact is: under its full source path, so that names do not collide */
export function artifactPath(sourcePath: string, contract: string): string {
  return `out/${sourcePath.replace(/^\/+/, "").replace(/:/g, "_")}/${contract}.json`;
}

/** Compiles the sources, with the Test base, into a project for `hevm test --root` */
export function compileProject(solc: Soljson, sources: Source[], settings?: CompileSettings): Project {
  const all = [...sources, testBase];
  const out = compileStandard(solc, all, settings);
  const errors: CompileError[] = (out.errors ?? []).map((e) => ({
    severity: e.severity,
    message: e.message,
    formatted: e.formattedMessage,
    file: e.sourceLocation?.file,
    start: e.sourceLocation?.start,
    end: e.sourceLocation?.end,
  }));
  const files: Record<string, string | null> = Object.fromEntries(all.map((s) => [s.path, s.content]));
  files["out/build-info"] = null;
  for (const [path, contracts] of Object.entries(out.contracts ?? {})) {
    const src = out.sources![path]!;
    for (const [name, c] of Object.entries(contracts)) {
      files[artifactPath(path, name)] = JSON.stringify({
        abi: c.abi,
        storageLayout: c.storageLayout,
        bytecode: { object: "0x" + c.evm.bytecode.object, sourceMap: c.evm.bytecode.sourceMap },
        deployedBytecode: {
          object: "0x" + c.evm.deployedBytecode.object,
          sourceMap: c.evm.deployedBytecode.sourceMap,
          immutableReferences: c.evm.deployedBytecode.immutableReferences ?? {},
        },
        methodIdentifiers: c.evm.methodIdentifiers ?? {},
        ast: src.ast,
        id: src.id,
      });
    }
  }
  return { errors, files };
}
