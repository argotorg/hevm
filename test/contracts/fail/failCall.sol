// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";

contract SolidityTest is Test {
    // forge-std's fail() sets a flag instead of reverting
    function prove_fail_called(uint256 x) public {
        if (x == 7) fail();
    }
}
