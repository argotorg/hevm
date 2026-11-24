// A first test of a verified contract: it deploys one, for hevm to check properties of.
import type { AbiParam, VerifiedContract } from "./sourcify";

/** A value of the type for the constructor, which one may want to change */
function placeholder(p: AbiParam): string | undefined {
  const t = p.type;
  if (t.endsWith("]") || t.startsWith("tuple")) return undefined;
  if (/^u?int\d*$/.test(t)) return "1";
  if (t === "address") return "address(this)";
  if (t === "bool") return "false";
  if (t === "string" || t === "bytes") return '""';
  const m = /^bytes(\d+)$/.exec(t);
  return m ? `bytes${m[1]}(0)` : undefined;
}

export const starterPath = (c: VerifiedContract) => `test/${c.name}.t.sol`;

export function starterTest(c: VerifiedContract): string {
  const [major, minor] = c.version.split(".");
  const args = c.constructorInputs.map((p) => placeholder(p));
  const deploy = args.every((a) => a !== undefined)
    ? `target = new ${c.name}(${args.join(", ")});`
    : `// target = new ${c.name}(...);`;
  const params = c.constructorInputs.map((p) => `${p.type}${p.name ? ` ${p.name}` : ""}`).join(", ");
  const note = !c.constructorInputs.length
    ? ""
    : args.every((a) => a !== undefined)
      ? `\n        // the constructor takes (${params}): these are placeholders`
      : `\n        // the constructor takes (${params}): fill them in`;
  return `// SPDX-License-Identifier: UNLICENSED
pragma solidity >=${major}.${minor}.0;

import {Test} from "hevm/Test.sol";
import {${c.name}} from "${c.path}";

// hevm proves the prove_ functions here for all their arguments, and checks the invariant_
// functions after every sequence of up to two calls to the contracts setUp() deploys
contract ${c.name}Test is Test {
    ${c.name} target;

    function setUp() public {${note}
        ${deploy}
    }

    // an example to start from: a property of ${c.name} that must hold for every x
    function prove_example(uint256 x) public {
        // call target here, then assert what must hold
        assert(x == x);
    }

    // after any calls to target, from anyone, with any arguments, this must hold
    // function invariant_example() public view {
    //     assert(...);
    // }
}
`;
}
