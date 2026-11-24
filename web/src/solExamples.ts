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
];
