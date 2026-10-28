// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";
import {StdInvariant} from "forge-std/StdInvariant.sol";

contract Counter {
    uint256 public count;

    function incr(uint256 x) public {
        require(x <= count);
        count += 1;
    }

    function reset() public {
        count = 0;
    }
}

contract CounterTest is Test {
    Counter c;

    function setUp() public {
        c = new Counter();
    }

    // two calls of incr break it
    function invariant_below_two() public view {
        assertLt(c.count(), 2);
    }
}

// from the ItyFuzz paper (Figure 2), as in halmos' examples
contract SimpleState {
    uint256 counter = 0;

    function incr(uint256 x) public {
        require(x <= counter);
        counter += 1;
    }

    function decr(uint256 x) public {
        require(x >= counter);
        counter -= 1;
    }

    function buggy() public view returns (bool) {
        return counter == 10;
    }
}

contract SimpleStateTest is Test {
    SimpleState target;

    function setUp() public {
        target = new SimpleState();
    }

    function invariant_buggy() public view {
        assertFalse(target.buggy());
    }
}

// the caller of take() must be the one that claimed
contract Owned {
    address public owner;
    bool public taken;

    function claim() public {
        require(owner == address(0));
        owner = msg.sender;
    }

    function take() public {
        require(msg.sender == owner);
        taken = true;
    }
}

contract OwnedTest is Test {
    Owned o;

    function setUp() public {
        o = new Owned();
    }

    function invariant_not_taken() public view {
        assertFalse(o.taken());
    }
}

contract Unsupported {
    uint256 public x;

    function setX(uint256[] calldata xs) public {
        x = xs.length;
    }
}

// a function that cannot be called is a warning
contract UnsupportedTest is Test {
    Unsupported u;

    function setUp() public {
        u = new Unsupported();
    }

    function invariant_zero() public view {
        assertEq(u.x(), 0);
    }
}

contract Spread {
    event Up();
    event Down();
    uint256 public last;

    function put(uint256 x, uint256 y) public {
        if (x > y) emit Up();
        else emit Down();
        last = x;
    }
}

// the counterexample comes from a merged state
contract SpreadTest is Test {
    Spread s;

    function setUp() public {
        s = new Spread();
    }

    function invariant_last_small() public view {
        assertLt(s.last(), 1000);
    }
}
