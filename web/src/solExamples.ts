export interface SolExample {
  name: string;
  source: string;
}

export const solExamples: SolExample[] = [
  {
    name: "Assertions",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

// hevm tries to break every prove_ function, for all arguments
contract Example is Test {
    function prove_linear(uint256 x) public pure {
        unchecked {
            assert(x * 3 + 7 != 100);
        }
    }

    function prove_fits(uint8 a, uint8 b) public pure {
        assert(uint16(a) + uint16(b) <= 510);
    }
}
`,
  },
  {
    name: "Token with a bug",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

contract Token {
    mapping(address => uint256) public balanceOf;

    constructor() {
        balanceOf[msg.sender] = 1000;
    }

    function transfer(address to, uint256 amount) external {
        uint256 fromBalance = balanceOf[msg.sender];
        uint256 toBalance = balanceOf[to];
        require(fromBalance >= amount, "insufficient balance");
        balanceOf[msg.sender] = fromBalance - amount;
        balanceOf[to] = toBalance + amount;
    }
}

contract TokenTest is Test {
    Token token = new Token();

    // a transfer must not change the total of the two balances
    function prove_transfer(address to, uint256 amount) public {
        uint256 before = token.balanceOf(address(this)) + token.balanceOf(to);
        token.transfer(to, amount);
        assert(token.balanceOf(address(this)) + token.balanceOf(to) == before);
    }
}
`,
  },
  {
    name: "Failure in a called contract",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

contract Vault {
    uint256 public total;

    function deposit(uint256 amount) external {
        total += amount;
        assert(total < 1000);
    }
}

contract VaultTest is Test {
    Vault vault = new Vault();

    function prove_deposit(uint256 amount) public {
        vault.deposit(amount);
    }
}
`,
  },
  {
    name: "Math library",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

library MathLib {
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }

    // rounds up, but a + b - 1 can wrap around
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        unchecked {
            return (a + b - 1) / b;
        }
    }

    function abs(int256 x) internal pure returns (uint256) {
        unchecked {
            return uint256(x >= 0 ? x : -x);
        }
    }

    function clamp(uint256 x, uint256 lo, uint256 hi) internal pure returns (uint256) {
        return min(max(x, lo), hi);
    }
}

contract MathTest is Test {
    function prove_min_max(uint256 a, uint256 b) public pure {
        assert(MathLib.min(a, b) <= MathLib.max(a, b));
        assert(MathLib.min(a, b) + MathLib.max(a, b) == a + b || a + b < a);
    }

    function prove_ceilDiv(uint256 a, uint256 b) public pure {
        require(b > 0);
        uint256 q = MathLib.ceilDiv(a, b);
        assert(q * b >= a);
    }

    function prove_abs(int256 x) public pure {
        assert(MathLib.abs(x) <= uint256(type(int256).max));
    }

    function prove_clamp(uint256 x, uint256 lo, uint256 hi) public pure {
        require(lo <= hi);
        uint256 c = MathLib.clamp(x, lo, hi);
        assert(lo <= c && c <= hi);
    }

    function prove_clamp_keeps(uint256 x, uint256 lo, uint256 hi) public pure {
        require(lo <= x && x <= hi);
        assert(MathLib.clamp(x, lo, hi) == x);
    }

    function prove_min_commutes(uint256 a, uint256 b) public pure {
        assert(MathLib.min(a, b) == MathLib.min(b, a));
    }
}
`,
  },
  {
    name: "Sorting network",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

// sorts three numbers with three compare-and-swaps: hevm explores every path
contract SortTest is Test {
    function sort3(uint256 a, uint256 b, uint256 c) internal pure returns (uint256, uint256, uint256) {
        if (a > b) (a, b) = (b, a);
        if (b > c) (b, c) = (c, b);
        if (a > b) (a, b) = (b, a);
        return (a, b, c);
    }

    function prove_sorted(uint256 a, uint256 b, uint256 c) public pure {
        (uint256 x, uint256 y, uint256 z) = sort3(a, b, c);
        assert(x <= y && y <= z);
    }

    function prove_permutation(uint256 a, uint256 b, uint256 c) public pure {
        (uint256 x, uint256 y, uint256 z) = sort3(a, b, c);
        unchecked {
            assert(x + y + z == a + b + c);
            assert(x ^ y ^ z == a ^ b ^ c);
        }
    }
}
`,
  },
  {
    name: "Bit tricks",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

contract BitsTest is Test {
    // the average without the overflow of (a + b) / 2
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        return (a & b) + ((a ^ b) >> 1);
    }

    function prove_average(uint128 a, uint128 b) public pure {
        assert(average(a, b) == (uint256(a) + uint256(b)) / 2);
    }

    function isPowerOfTwo(uint256 x) internal pure returns (bool) {
        unchecked {
            return x & (x - 1) == 0;
        }
    }

    // 0 is not a power of two, but the trick says it is
    function prove_powerOfTwo(uint256 x) public pure {
        if (isPowerOfTwo(x)) assert(x != 0);
    }
}
`,
  },
  {
    name: "Access control",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

contract Vault {
    address public owner;
    uint256 public fee;

    constructor() {
        owner = msg.sender;
    }

    function setFee(uint256 newFee) external {
        require(msg.sender == owner, "not owner");
        require(newFee <= 100, "fee too high");
        fee = newFee;
    }

    // forgot the owner check
    function setOwner(address newOwner) external {
        owner = newOwner;
    }
}

contract Stranger {
    function takeOver(Vault v) external {
        v.setOwner(address(this));
        v.setFee(100);
    }
}

contract VaultTest is Test {
    Vault vault = new Vault();
    Stranger stranger = new Stranger();

    function prove_fee_capped(uint256 newFee) public {
        try vault.setFee(newFee) {} catch {}
        assert(vault.fee() <= 100);
    }

    function prove_only_owner_sets_fee() public {
        try stranger.takeOver(vault) {} catch {}
        assert(vault.owner() == address(this));
    }
}
`,
  },
];
