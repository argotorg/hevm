// Verified contracts from saved Sourcify answers, compiled with their own solc, and tested with hevm.wasm.
import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { beforeAll, describe, expect, it } from "vitest";
import { runHevm } from "../src/hevm";
import { importClosure } from "../src/imports";
import { describeResult, parseTestOutput } from "../src/results";
import { compileProject, evalSoljson, solcVersion } from "../src/solc";
import { artifactPath } from "../src/solc";
import { fetchVerified, parseTarget, readVerified, sameAsDeployed, type VerifiedContract } from "../src/sourcify";
import { sourcifyExamples } from "../src/sourcifyExamples";
import { starterPath, starterTest } from "../src/starter";
import { hasSoljson, soljsonText } from "./soljsonCache";

const fixture = (name: string) => JSON.parse(readFileSync(new URL(`fixtures/sourcify/${name}.json`, import.meta.url), "utf8"));
const factory = readVerified("1", "0x1F98431c8aD98523631AE4a59f267346ea31F984", fixture("univ3factory"));
const weth = readVerified("1", "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2", fixture("weth9"));

const wasmPath = fileURLToPath(new URL("../../dist-wasm/hevm.wasm", import.meta.url));
let module: WebAssembly.Module;
beforeAll(async () => {
  if (!existsSync(wasmPath)) throw new Error(`${wasmPath} is missing: run wasm/build.sh first`);
  module = await WebAssembly.compile(readFileSync(wasmPath));
});

describe("Sourcify", () => {
  it("reads a verified contract", () => {
    expect(factory).toMatchObject({
      name: "UniswapV3Factory",
      path: "contracts/UniswapV3Factory.sol",
      version: "0.7.6+commit.7338295f",
      constructorInputs: [],
      implementations: [],
    });
    expect(factory.settings).toMatchObject({ optimizer: { enabled: true, runs: 800 }, evmVersion: "istanbul" });
    expect(weth).toMatchObject({ name: "WETH9", path: "WETH9.sol", version: "0.4.19+commit.c4cbbb05" });
    // the factory's immutable is its own address, and WETH9's metadata a swarm hash
    expect(factory.deployed!.runtime.ignore).toEqual([{ start: 1361, length: 32 }]);
    expect(weth.deployed!.runtime.ignore).toEqual([{ start: 3081, length: 43 }]);
    expect(weth.deployed!.creation!.ignore).toEqual([{ start: 3461, length: 43 }]);
    expect(factory.deployed!.runtime.code.length).toBe(2 * 24535);
  });

  it("takes an address, or a link with the chain", () => {
    expect(parseTarget(" 0x1F98431c8aD98523631AE4a59f267346ea31F984 ")).toEqual({ address: "0x1F98431c8aD98523631AE4a59f267346ea31F984" });
    expect(parseTarget("https://repo.sourcify.dev/8453/0x1F98431c8aD98523631AE4a59f267346ea31F984"))
      .toEqual({ chainId: "8453", address: "0x1F98431c8aD98523631AE4a59f267346ea31F984" });
    expect(parseTarget("0x1234")).toBeUndefined();
  });

  it("asks once per contract, for only the fields needed, and explains failures", async () => {
    const urls: string[] = [];
    const get = (async (url: string) => {
      urls.push(url);
      return url.includes("0x00000000000000000000000000000000000000aa")
        ? new Response("{}", { status: 404 })
        : new Response(JSON.stringify(fixture("weth9")), { status: 200 });
    }) as typeof fetch;
    const a = await fetchVerified("1", "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2", get);
    const b = await fetchVerified("1", "0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2", get);
    expect(b).toBe(a);
    expect(urls).toEqual(["https://sourcify.dev/server/v2/contract/1/0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2?fields=sources,compilation,abi,proxyResolution,"
      + "runtimeBytecode.onchainBytecode,runtimeBytecode.immutableReferences,runtimeBytecode.cborAuxdata,"
      + "creationBytecode.recompiledBytecode,creationBytecode.cborAuxdata"]);
    await expect(fetchVerified("1", "0x00000000000000000000000000000000000000aa", get)).rejects.toThrow(/not verified on Sourcify for chain 1/);
    expect(() => readVerified("1", "0x00", { compilation: { language: "Vyper", compilerVersion: "0.3.10", compilerSettings: {}, fullyQualifiedName: "a.vy:A" }, sources: {} }))
      .toThrow(/Vyper contracts are not supported yet/);
  });
});

async function testVerified(c: VerifiedContract, test: string) {
  const files = { ...c.sources, [starterPath(c)]: test };
  const closure = importClosure(files, [c.path, starterPath(c)], (c.settings.remappings as string[] | undefined) ?? []);
  const solc = evalSoljson(soljsonText(c.version));
  expect(solcVersion(solc)).toMatch(new RegExp(`^${c.version.replace("+", "\\+")}`));
  const project = compileProject(solc, closure.map((path) => ({ path, content: files[path]! })), { solc: c.settings });
  expect(project.errors.filter((e) => e.severity === "error").map((e) => e.formatted)).toEqual([]);
  const run = await runHevm(module, ["test", "--root", "/"], { files: project.files });
  return Object.fromEntries(parseTestOutput(run.stdout).map((r) => [r.name, r]));
}

describe.skipIf(!hasSoljson(factory.version))("a verified contract with many files, compiled with solc 0.7.6", () => {
  it("passes its starter test, and fails where a test of it fails", async () => {
    const test = starterTest(factory).replace(
      "    // after any calls",
      `    function prove_owner_is_deployer() public view {
        assert(target.owner() == address(0x1234));
    }

    // after any calls`,
    );
    const res = await testVerified(factory, test);
    expect(res["prove_example(uint256)"]?.status).toBe("pass");
    const fail = res["prove_owner_is_deployer()"]!;
    expect(fail.status).toBe("fail");
    const line = test.split("\n").findIndex((l) => l.includes("assert(target.owner()")) + 1;
    expect(fail.counterexamples[0]!.at).toMatchObject({ file: "test/UniswapV3Factory.t.sol", line });
  });
});

// the contract's code, compiled from its files as they are, or with one edited
function compiledCode(c: VerifiedContract, edit?: (source: string) => string): { runtime: string; creation: string } {
  const files = { ...c.sources, ...(edit && { [c.path]: edit(c.sources[c.path]!) }) };
  const closure = importClosure(files, [c.path], (c.settings.remappings as string[] | undefined) ?? []);
  const project = compileProject(evalSoljson(soljsonText(c.version)), closure.map((path) => ({ path, content: files[path]! })), { solc: c.settings });
  const a = JSON.parse(project.files[artifactPath(c.path, c.name)]!);
  return { runtime: a.deployedBytecode.object, creation: a.bytecode.object };
}

describe("the code compiled, and the code deployed", () => {
  it.skipIf(!hasSoljson(factory.version))("are the same for Uniswap V3's factory, unless its code is edited", () => {
    expect(sameAsDeployed(compiledCode(factory), factory.deployed!)).toBe(true);
    expect(sameAsDeployed(compiledCode(factory, (s) => `// a comment\n${s}`), factory.deployed!)).toBe(true);
    expect(sameAsDeployed(compiledCode(factory, (s) => s.replace("require(fee < 1000000);", "require(fee < 2000000);")), factory.deployed!)).toBe(false);
  });

  it.skipIf(!hasSoljson(weth.version))("are the same for WETH9, but for its metadata", () => {
    expect(sameAsDeployed(compiledCode(weth), weth.deployed!)).toBe(true);
    // an initial value is the constructor's: the runtime code stays, the creation code changes
    const decimals = compiledCode(weth, (s) => s.replace("uint8  public decimals = 18;", "uint8  public decimals = 17;"));
    expect(sameAsDeployed({ runtime: decimals.runtime, creation: compiledCode(weth).creation }, weth.deployed!)).toBe(true);
    expect(sameAsDeployed(decimals, weth.deployed!)).toBe(false);
    expect(sameAsDeployed(compiledCode(weth, (s) => s.replace("require(balanceOf[msg.sender] >= wad);", "require(balanceOf[msg.sender] > wad);")), weth.deployed!)).toBe(false);
  });
});

describe.skipIf(!hasSoljson(factory.version))("the Sourcify tab's example, Uniswap V3's factory", () => {
  it("has properties hevm proves", async () => {
    const res = await testVerified(factory, sourcifyExamples[0]!.test);
    const status = Object.fromEntries(Object.entries(res).map(([name, r]) => [name, r.status]));
    expect(status).toEqual({
      "prove_initial_fee_tiers(uint24)": "pass",
      "prove_enable_fee(uint24,int24)": "pass",
      "prove_enable_fee_exactly_when_valid(uint24,int24)": "pass",
      "prove_create_pool()": "pass",
      "prove_one_pool_per_pair()": "pass",
    });
  });
});

describe.skipIf(!hasSoljson(weth.version))("a verified contract from 2017, compiled with solc 0.4.19", () => {
  it("passes its starter test, and fails at a failed assert", async () => {
    const test = starterTest(weth).replace("assert(x == x);", "target.deposit.value(x)();\n        assert(target.balanceOf(this) != 7);");
    const res = await testVerified(weth, test);
    const t = res["prove_example(uint256)"]!;
    expect(t.status).toBe("fail");
    expect(t.counterexamples[0]).toMatchObject({ calldata: "prove_example(7)", result: "Unrecognized opcode: 254" });
    expect(describeResult(t.counterexamples[0]!.result)).toBe("INVALID opcode: a failed assert, before Solidity 0.8");
  });
});
