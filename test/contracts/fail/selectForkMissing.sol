// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";

contract SolidityTest is Test {
    function prove_select_missing_fork(uint256 x) public {
        if (x == 7) vm.selectFork(5);
    }
}
