// Picks the two programs of an equivalence check out of compiled Solidity.
import { functions, type AbiFunction } from "./abi";
import { progressPath } from "./hevm";
import { artifactPath, type CompileError, type CompileSettings, type Project, type Source } from "./solc";

/** Two contracts, or one compiled in two ways */
export type EqMode = "contracts" | "optimizer" | "via-ir";

export interface EqProgram {
  label: string;
  code: string;
  abi: AbiFunction[];
  selectors: Record<string, string>;
}

export const eqSourcePath = "src/Equivalence.sol";

type Compile = (sources: Source[], settings?: CompileSettings) => Project | Promise<Project>;

/** The contracts a source defines, by a look at it, before it compiles */
export function contractNames(source: string): string[] {
  const noComments = source.replace(/\/\/.*$|\/\*[\s\S]*?\*\//gm, "");
  return [...noComments.matchAll(/^\s*contract\s+([A-Za-z_$][\w$]*)/gm)].map((m) => m[1]!);
}

function program(project: Project, contract: string, label: string): EqProgram {
  const artifact = project.files[artifactPath(eqSourcePath, contract)];
  if (!artifact) throw new Error(`no contract ${contract} in the source`);
  const a = JSON.parse(artifact) as {
    abi: unknown[];
    deployedBytecode: { object: string };
    methodIdentifiers: Record<string, string>;
  };
  return { label, code: a.deployedBytecode.object, abi: functions(a.abi), selectors: a.methodIdentifiers };
}

export async function eqPrograms(
  compile: Compile,
  source: string,
  mode: EqMode,
  a: string,
  b: string,
): Promise<{ errors: CompileError[] } | { programs: [EqProgram, EqProgram] }> {
  const sources = [{ path: eqSourcePath, content: source }];
  const [settingsA, settingsB, labelA, labelB]: [CompileSettings, CompileSettings, string, string] =
    mode === "optimizer" ? [{ optimize: false }, { optimize: true }, `${a}, optimizer off`, `${a}, optimizer on`]
    : mode === "via-ir" ? [{}, { viaIR: true, optimize: true }, `${a}, legacy codegen`, `${a}, via-IR`]
    : [{}, {}, a, b];
  const projectA = await compile(sources, settingsA);
  const projectB = mode === "contracts" ? projectA : await compile(sources, settingsB);
  const errors = [...projectA.errors, ...(projectB === projectA ? [] : projectB.errors)].filter((e) => e.severity === "error");
  if (errors.length) return { errors };
  return { programs: [program(projectA, a, labelA), program(projectB, mode === "contracts" ? b : a, labelB)] };
}

export function eqArgs(a: EqProgram, b: EqProgram): string[] {
  return ["equivalence", "--code-a", a.code, "--code-b", b.code, "--progress-log", progressPath];
}
