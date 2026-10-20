// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";

contract C {
    error E(uint256);
    function f(uint256 x) external pure { revert E(x); }
}

// none of these may pass: each needs a cheatcode to act on symbolic data it cannot handle
contract SolidityTest is Test {
    C c;
    function setUp() public { c = new C(); }

    function prove_assertEq_symbolic_bytes(uint256 x) public pure {
        if (x > 10) assertEq(abi.encodePacked(x), abi.encodePacked(uint256(5)));
    }

    function prove_store_symbolic_address(address a, bool b) public {
        if (b) {
            vm.store(a, bytes32(0), bytes32(uint256(1)));
            assertTrue(false);
        }
    }

    function prove_expectRevert_symbolic_data(uint256 x, bool b) public {
        if (b) {
            vm.expectRevert(abi.encodeWithSelector(C.E.selector, x));
            c.f(x ^ 1);
        }
    }
}
