// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.18;

import {Test} from "forge-std/Test.sol";

contract Reverter {
    error CustomError();

    function revertWithMessage(string memory message) public pure {
        revert(message);
    }

    function doNotRevert() public pure {}

    function revertWithCustomError() public pure {
        revert CustomError();
    }
}

contract SolidityTest is Test {
    function prove_expectRevert_some_branches_dont_revert(uint256 x) public {
        Reverter reverter = new Reverter();
        vm.expectRevert();
        if (x == 0) reverter.doNotRevert();
        else reverter.revertWithMessage("foo");
    }

    function prove_expectRevert_message_mismatch(uint256 x) public {
        Reverter reverter = new Reverter();
        vm.expectRevert("expected");
        if (x == 0) reverter.revertWithMessage("expected");
        else reverter.revertWithMessage("wrong");
    }

    function prove_expectRevert_wrong_reverter(uint256 x) public {
        Reverter a = new Reverter();
        Reverter b = new Reverter();
        vm.expectRevert(address(a));
        if (x == 0) a.revertWithMessage("foo");
        else b.revertWithMessage("foo");
    }

    function prove_expectPartialRevert_wrong_selector(bool useCustom) public {
        Reverter reverter = new Reverter();
        vm.expectPartialRevert(Reverter.CustomError.selector);
        if (useCustom) reverter.revertWithCustomError();
        else reverter.revertWithMessage("any");
    }
}
