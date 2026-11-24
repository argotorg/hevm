// Verified contracts from saved Sourcify answers, compiled with their own solc, and tested with hevm.wasm.
import { existsSync, readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { beforeAll, describe, expect, it } from "vitest";
import { runHevm } from "../src/hevm";
import { importClosure } from "../src/imports";
import { parseTestOutput } from "../src/results";
import { compileProject, evalSoljson, solcVersion } from "../src/solc";
import { fetchVerified, parseTarget, readVerified, type VerifiedContract } from "../src/sourcify";
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
    expect(urls).toEqual(["https://sourcify.dev/server/v2/contract/1/0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2?fields=sources,compilation,abi,proxyResolution"]);
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

describe.skipIf(!hasSoljson(weth.version))("a verified contract from 2017, compiled with solc 0.4.19", () => {
  it("passes its starter test, and fails at a failed assert", async () => {
    const test = starterTest(weth).replace("assert(x == x);", "target.deposit.value(x)();\n        assert(target.balanceOf(this) != 7);");
    const res = await testVerified(weth, test);
    const t = res["prove_example(uint256)"]!;
    expect(t.status).toBe("fail");
    expect(t.counterexamples[0]).toMatchObject({ calldata: "prove_example(7)", result: "Unrecognized opcode: 254" });
  });
});
