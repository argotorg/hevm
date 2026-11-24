import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { importClosure, importsOf, resolveImport } from "../src/imports";

describe("imports", () => {
  it("are found in every form, not in comments", () => {
    const src = `import "a.sol";
import * as B from './b.sol';
import {C, D as E} from "../c.sol";
import "f.sol" as F;
// import "commented.sol";
/* import "also-commented.sol"; */
string constant s = "import x";`;
    expect(importsOf(src)).toEqual(["a.sol", "./b.sol", "../c.sol", "f.sol"]);
  });

  it("are resolved as solc does", () => {
    expect(resolveImport("contracts/pool/A.sol", "./B.sol")).toBe("contracts/pool/B.sol");
    expect(resolveImport("contracts/pool/A.sol", "../lib/C.sol")).toBe("contracts/lib/C.sol");
    expect(resolveImport("contracts/A.sol", "@oz/token/ERC20.sol")).toBe("@oz/token/ERC20.sol");
    expect(resolveImport("contracts/A.sol", "@oz/token/ERC20.sol", ["@oz/=lib/openzeppelin/contracts/"]))
      .toBe("lib/openzeppelin/contracts/token/ERC20.sol");
    expect(resolveImport("src/A.sol", "x/Y.sol", ["x/=a/", "x/Y=b/Y"])).toBe("b/Y.sol");
    expect(resolveImport("other/A.sol", "x/Y.sol", ["src/:x/=a/"])).toBe("x/Y.sol");
  });

  it("make the closure of a verified contract, not all its compilation's sources", () => {
    const res = JSON.parse(readFileSync(new URL("fixtures/sourcify/univ3factory.json", import.meta.url), "utf8"));
    const files = Object.fromEntries(Object.entries(res.sources).map(([p, s]) => [p, (s as { content: string }).content]));
    const closure = importClosure(files, ["contracts/UniswapV3Factory.sol"]);
    expect(closure[0]).toBe("contracts/UniswapV3Factory.sol");
    expect(closure).toContain("contracts/libraries/TickMath.sol");
    expect(closure).not.toContain("contracts/core-contracts/UniswapV3Pool.sol");
    expect(closure.length).toBe(33);
    expect(Object.keys(files).length).toBe(36);
  });
});
