import { describe, expect, it } from "vitest";
import { eqExamples } from "../src/eqExamples";
import { decodeShare, encodeShare, type Shared } from "../src/share";
import { solExamples } from "../src/solExamples";

describe("links", () => {
  const round = async (s: Shared) => decodeShare("#" + (await encodeShare(s)));

  it("name examples readably", async () => {
    expect(await encodeShare({ tab: "sol", example: "Unsafe downcast" })).toBe("tab=sol&example=Unsafe+downcast");
    expect(await round({ tab: "eq", example: "A cheaper average" })).toEqual({ tab: "eq", example: "A cheaper average" });
  });

  it("carry edited code, compressed", async () => {
    const source = solExamples.find((e) => e.name === "Math library")!.source + "\n// édité ✓\n";
    const hash = await encodeShare({ tab: "sol", source });
    expect(hash.length).toBeLessThan(source.length / 2);
    expect(hash).toMatch(/^tab=sol&s=[\w-]+$/);
    expect(await round({ tab: "sol", source })).toEqual({ tab: "sol", source });
  });

  it("carry the equivalence settings and the bytecode tab", async () => {
    const eq: Shared = { tab: "eq", source: eqExamples[0]!.source, mode: "via-ir", a: "Reference", b: "BranchFree" };
    expect(await round(eq)).toEqual(eq);
    const bytecode: Shared = { tab: "bytecode", request: { mode: "exec", code: "0x6001", calldata: "0x12", sig: "" } };
    expect(await round(bytecode)).toEqual(bytecode);
  });

  it("ignore what is not theirs", async () => {
    for (const hash of ["", "#", "#intro", "#tab=sol", "#tab=sol&s=not-deflate", "#tab=eq&s=" + (await encodeShare({ tab: "sol", source: "x" })).slice(10), "#tab=nope&example=x"]) {
      expect(await decodeShare(hash), hash).toBeUndefined();
    }
  });
});
