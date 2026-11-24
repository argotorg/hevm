// Compiles with soljson (solc's emscripten build) and lays the output out as forge's out/
// directory, which `hevm test` reads.

export interface Soljson {
  cwrap(name: string, ret: string | null, args: string[]): (...args: unknown[]) => unknown;
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
pragma solidity >=0.8.0;

// Contracts inheriting this are tests: hevm proves their prove_ functions
abstract contract Test {
    bool public IS_TEST = true;
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
  evm: { bytecode: Bytecode; deployedBytecode: Bytecode };
}

export function solcVersion(solc: Soljson): string {
  return solc.cwrap("solidity_version", "string", [])() as string;
}

export function compileStandard(solc: Soljson, sources: Source[]): StandardOutput {
  const input = {
    language: "Solidity",
    sources: Object.fromEntries(sources.map((s) => [s.path, { content: s.content }])),
    settings: {
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
          ],
          "": ["ast"],
        },
      },
    },
  };
  const compile = solc.cwrap("solidity_compile", "string", ["string", "number", "number"]);
  const out = JSON.parse(compile(JSON.stringify(input), 0, 0) as string) as StandardOutput;
  solc.cwrap("solidity_reset", null, [])();
  return out;
}

export interface Project {
  errors: CompileError[];
  /** paths under the project root and their contents, or null for an empty directory */
  files: Record<string, string | null>;
}

/** Compiles the sources, with the Test base, into a project for `hevm test --root` */
export function compileProject(solc: Soljson, sources: Source[]): Project {
  const all = [...sources, testBase];
  const out = compileStandard(solc, all);
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
    const dir = `out/${path.split("/").pop()}`;
    for (const [name, c] of Object.entries(contracts)) {
      files[`${dir}/${name}.json`] = JSON.stringify({
        abi: c.abi,
        storageLayout: c.storageLayout,
        bytecode: { object: "0x" + c.evm.bytecode.object, sourceMap: c.evm.bytecode.sourceMap },
        deployedBytecode: {
          object: "0x" + c.evm.deployedBytecode.object,
          sourceMap: c.evm.deployedBytecode.sourceMap,
          immutableReferences: c.evm.deployedBytecode.immutableReferences ?? {},
        },
        ast: src.ast,
        id: src.id,
      });
    }
  }
  return { errors, files };
}
