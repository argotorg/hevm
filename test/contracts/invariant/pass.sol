// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";
import {StdInvariant} from "forge-std/StdInvariant.sol";

contract Vault {
    mapping(address => uint256) public balanceOf;
    uint256 public total;

    function deposit(uint256 amount) public {
        balanceOf[msg.sender] += amount;
        total += amount;
    }

    function withdraw(uint256 amount) public {
        balanceOf[msg.sender] -= amount;
        total -= amount;
    }

    function transfer(address to, uint256 amount) public {
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
    }
}

contract VaultTest is Test {
    Vault v;

    function setUp() public {
        v = new Vault();
        targetContract(address(v));
    }

    function invariant_total_covers(address who) public view {
        assertGe(v.total(), v.balanceOf(who));
    }
}

contract Switch {
    bool public on;

    function flip() public {
        on = true;
    }

    function noop() public {}
}

// only the selected functions are called
contract SwitchTest is Test {
    Switch s;

    function setUp() public {
        s = new Switch();
        bytes4[] memory selectors = new bytes4[](1);
        selectors[0] = Switch.noop.selector;
        targetSelector(StdInvariant.FuzzSelector({addr: address(s), selectors: selectors}));
    }

    function invariant_off() public view {
        assertFalse(s.on());
    }
}

contract Counter {
    uint256 public count;

    function incr() public {
        count += 1;
    }
}

// as deep as the sequences go, which is 2 calls by default
contract CounterTest is Test {
    Counter c;

    function setUp() public {
        c = new Counter();
    }

    function invariant_below_three() public view {
        assertLt(c.count(), 3);
    }
}

contract Toggle {
    bool public on;

    function flip() public {
        on = !on;
    }
}

// flipping twice gives a state seen before
contract ToggleTest is Test {
    Toggle t;

    function setUp() public {
        t = new Toggle();
    }

    function invariant_bool() public view {
        bool on = t.on();
        assertTrue(on || !on);
    }
}

contract Cycle {
    bool public both;

    function set(uint256 x, uint256 y, uint256 z) public {
        if (x < y && y < z && z < x) both = true;
    }
}

// the state after the infeasible branch is not reached
contract CycleTest is Test {
    Cycle p;

    function setUp() public {
        p = new Cycle();
    }

    function invariant_neither() public view {
        assertFalse(p.both());
    }
}
