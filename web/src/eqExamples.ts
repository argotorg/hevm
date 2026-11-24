import type { EqMode } from "./equivalence";

export interface EqExample {
  name: string;
  mode: EqMode;
  a: string;
  b: string;
  source: string;
}

export const eqExamples: EqExample[] = [
  {
    name: "Branch-free min and max",
    mode: "contracts",
    a: "Reference",
    b: "BranchFree",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// hevm checks that both contracts behave the same on every call, for all arguments

contract Reference {
    function max(uint256 a, uint256 b) external pure returns (uint256) {
        return a > b ? a : b;
    }

    function min(uint256 a, uint256 b) external pure returns (uint256) {
        return a < b ? a : b;
    }
}

// the same without jumps: x ^ ((x ^ y) * cond) is y if cond is 1, x if it is 0
contract BranchFree {
    function max(uint256 a, uint256 b) external pure returns (uint256 r) {
        assembly { r := xor(a, mul(xor(a, b), gt(b, a))) }
    }

    function min(uint256 a, uint256 b) external pure returns (uint256 r) {
        assembly { r := xor(a, mul(xor(a, b), lt(b, a))) }
    }
}
`,
  },
  {
    name: "A cheaper average",
    mode: "contracts",
    a: "Simple",
    b: "Clever",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Simple {
    function average(uint256 a, uint256 b) external pure returns (uint256) {
        return (a + b) / 2;
    }
}

// never overflows, so it is not a drop-in replacement: hevm finds where the two differ
contract Clever {
    function average(uint256 a, uint256 b) external pure returns (uint256) {
        return (a & b) + ((a ^ b) >> 1);
    }
}
`,
  },
  {
    name: "Forgot the zero case",
    mode: "contracts",
    a: "Careful",
    b: "Forgetful",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// x & (~x + 1) is the lowest set bit of x: a power of two is just that bit
contract Careful {
    function isPowerOfTwo(uint256 x) external pure returns (bool) {
        unchecked {
            return x != 0 && x & (~x + 1) == x;
        }
    }
}

// x & (x - 1) clears the lowest set bit
contract Forgetful {
    function isPowerOfTwo(uint256 x) external pure returns (bool) {
        unchecked {
            return x & (x - 1) == 0;
        }
    }
}
`,
  },
  {
    name: "One comparison instead of two",
    mode: "contracts",
    a: "TwoComparisons",
    b: "OneComparison",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract TwoComparisons {
    function inRange(uint256 x, uint256 lo, uint256 hi) external pure returns (bool) {
        return lo <= x && x <= hi;
    }
}

// x - lo wraps around below lo, so one unsigned comparison checks both ends,
// as long as the range is not empty
contract OneComparison {
    function inRange(uint256 x, uint256 lo, uint256 hi) external pure returns (bool) {
        unchecked {
            return x - lo <= hi - lo;
        }
    }
}
`,
  },
  {
    name: "Does the optimizer change anything?",
    mode: "optimizer",
    a: "Fees",
    b: "Fees",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// one contract compiled twice, without and with solc's optimizer
contract Fees {
    uint256 constant BPS = 10_000;

    function fee(uint256 amount, uint16 rateBps) external pure returns (uint256) {
        require(rateBps <= 1_000, "rate too high");
        return amount * rateBps / BPS;
    }

    function split(uint256 amount) external pure returns (uint256 toOwner, uint256 toPool) {
        toOwner = amount / 3;
        toPool = amount - toOwner;
    }

    function clamp(int256 x, int256 lo, int256 hi) external pure returns (int256) {
        if (x < lo) return lo;
        if (x > hi) return hi;
        return x;
    }
}
`,
  },
  {
    name: "Legacy codegen vs via-IR",
    mode: "via-ir",
    a: "Packing",
    b: "Packing",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// one contract compiled by solc's two code generators
contract Packing {
    function pack(uint64 a, uint64 b, uint128 c) external pure returns (uint256) {
        return uint256(a) << 192 | uint256(b) << 128 | c;
    }

    function unpack(uint256 x) external pure returns (uint64 a, uint64 b, uint128 c) {
        a = uint64(x >> 192);
        b = uint64(x >> 128);
        c = uint128(x);
    }

    function total(uint256[3] calldata parts) external pure returns (uint256 sum) {
        for (uint256 i = 0; i < 3; i++) sum += parts[i];
    }
}
`,
  },
];
