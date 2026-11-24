export interface SolExample {
  name: string;
  source: string;
  /** where the dropdown lists it, if not with the plain examples */
  group?: "Invariants" | "Real bug patterns";
  /** the story behind it, shown above the source */
  story?: string;
}

export const solExamples: SolExample[] = [
  {
    name: "Find x, prove a bound",
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
  {
    name: "Supply invariant",
    group: "Invariants",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

contract Token {
    mapping(address => uint256) public balanceOf;
    uint256 public totalSupply;

    function mint(uint256 amount) external {
        balanceOf[msg.sender] += amount;
        totalSupply += amount;
    }

    function transfer(address to, uint256 amount) external {
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
    }

    function burn(uint256 amount) external {
        totalSupply -= amount;
    }
}

// hevm calls the token's functions in every order, with any arguments, and checks
// invariant_ functions after each sequence of calls: no fuzzing, no seeds
contract TokenTest is Test {
    Token token;
    address constant alice = address(0xa11ce);

    function setUp() public {
        token = new Token();
        targetSender(alice);
    }

    function invariant_supply() public view {
        assert(token.balanceOf(alice) <= token.totalSupply());
    }
}
`,
  },
  {
    name: "Re-initializable wallet (Parity, 2017)",
    group: "Real bug patterns",
    story:
      "In July 2017 an attacker called the Parity multisig wallet's initWallet a second time, " +
      "became the owner of three wallets, and took about 150,000 ETH, then some $30 million. " +
      "Nothing stopped initialization from running again.",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

contract Wallet {
    address public owner;

    // meant to run once, but nothing checks that it already ran
    function initWallet() external {
        owner = msg.sender;
    }

    uint256 public dailyLimit = 1 ether;

    function setDailyLimit(uint256 limit) external {
        require(msg.sender == owner, "not owner");
        dailyLimit = limit;
    }
}

contract WalletTest is Test {
    Wallet wallet;

    function setUp() public {
        wallet = new Wallet();
        wallet.initWallet();
    }

    // whoever calls in, the test contract stays the owner
    function invariant_owner() public view {
        assert(wallet.owner() == address(this));
    }
}
`,
  },
  {
    name: "Escrow state machine",
    group: "Invariants",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

contract Escrow {
    address public immutable buyer;
    address public immutable seller;
    bool public released;
    bool public refunded;

    constructor(address b, address s) {
        buyer = b;
        seller = s;
    }

    // the buyer confirms delivery: the seller gets paid
    function release() external {
        require(msg.sender == buyer, "only the buyer");
        require(!refunded, "already refunded");
        released = true;
    }

    // the seller cancels: the buyer gets the money back, but nothing checks that the
    // seller was not paid already
    function refund() external {
        require(msg.sender == seller, "only the seller");
        refunded = true;
    }
}

contract EscrowTest is Test {
    Escrow escrow;
    address constant buyer = address(0xb0b);
    address constant seller = address(0x5e11e7);

    function setUp() public {
        escrow = new Escrow(buyer, seller);
        targetSender(buyer);
        targetSender(seller);
    }

    // the money goes one way only
    function invariant_one_outcome() public view {
        assert(!(escrow.released() && escrow.refunded()));
    }
}
`,
  },
  {
    name: "Batch transfer overflow (BeautyChain, 2018)",
    group: "Real bug patterns",
    story:
      "In April 2018 someone called BeautyChain's batchTransfer with two receivers and a value of 2^255: " +
      "the total, receivers times value, wrapped around to 0 and passed the balance check, and each " +
      "receiver got 2^255 tokens out of nothing (CVE-2018-10299). Exchanges suspended the token.",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

// the core of BeautyChain's batchTransfer, written for Solidity 0.4, whose arithmetic
// wrapped around as unchecked arithmetic does now
contract Token {
    mapping(address => uint256) public balanceOf;

    constructor() {
        balanceOf[msg.sender] = 1_000 ether;
    }

    function batchTransfer(address[2] calldata receivers, uint256 value) external {
        unchecked {
            uint256 amount = receivers.length * value;
            require(value > 0 && balanceOf[msg.sender] >= amount);
            balanceOf[msg.sender] -= amount;
            for (uint256 i = 0; i < receivers.length; i++) {
                balanceOf[receivers[i]] += value;
            }
        }
    }
}

contract TokenTest is Test {
    // all 1,000 tokens are the test contract's: nobody can end up with more
    function prove_no_tokens_from_nothing(address a, address b, uint256 value) public {
        require(a != b && a != address(this) && b != address(this));
        Token token = new Token();
        token.batchTransfer([a, b], value);
        assert(token.balanceOf(a) <= 1_000 ether);
    }
}
`,
  },
  {
    name: "Unsafe downcast",
    group: "Real bug patterns",
    story:
      "A cast to a smaller integer type silently drops the high bits: uint128(2^128) is 0. Packing " +
      "balances into small types to save storage made this a recurring bug, and OpenZeppelin's " +
      "SafeCast library exists to catch it.",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

contract Staking {
    // two stakes fit in one storage slot
    mapping(address => uint128) public stakeOf;
    uint256 public totalStaked;

    function stake(uint256 amount) external {
        stakeOf[msg.sender] += uint128(amount);
        totalStaked += amount;
    }
}

contract StakingTest is Test {
    function prove_stake_recorded(uint256 amount) public {
        Staking staking = new Staking();
        staking.stake(amount);
        assert(staking.stakeOf(address(this)) == staking.totalStaked());
    }
}
`,
  },
  {
    name: "Share inflation (ERC-4626)",
    group: "Real bug patterns",
    story:
      "A vault's first depositor can mint a single share, then send tokens straight to the vault: " +
      "the next deposit's shares round down to zero, and the attacker's one share owns it all. This " +
      "inflation attack on ERC-4626 vaults is why OpenZeppelin's implementation adds virtual shares.",
    source: `// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Test} from "hevm/Test.sol";

contract Vault {
    mapping(address => uint256) public sharesOf;
    uint256 public totalShares;
    // what the vault holds: deposits, and anything sent to it directly
    uint256 public totalAssets;

    function deposit(uint256 assets) external returns (uint256 shares) {
        shares = totalShares == 0 ? assets : assets * totalShares / totalAssets;
        sharesOf[msg.sender] += shares;
        totalShares += shares;
        totalAssets += assets;
    }

    // a plain transfer of tokens to the vault, which makes every share worth more
    function donate(uint256 assets) external {
        totalAssets += assets;
    }
}

contract VaultTest is Test {
    function prove_deposit_gets_shares(uint256 donation, uint256 assets) public {
        require(assets > 0 && assets < 1e30 && donation < 1e30);
        Vault vault = new Vault();
        // the attacker gets in first, with 1 wei, and sends tokens directly
        vault.deposit(1);
        vault.donate(donation);
        // then someone deposits
        uint256 shares = vault.deposit(assets);
        assert(shares > 0);
    }
}
`,
  },
];
