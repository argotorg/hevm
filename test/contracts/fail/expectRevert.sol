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

    function revertWithoutReason() public pure {
        revert();
    }
}

contract WithArgError {
    error CustomError(uint256 x);
    function go() external pure {
        revert CustomError(42);
    }
}

contract SolidityTest is Test {
    function prove_expectRevert_some_branches_dont_revert(uint256 x) public {
        Reverter reverter = new Reverter();
        vm.expectRevert();
        if (x == 0) reverter.doNotRevert();
        else reverter.revertWithMessage("expected");
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
        if (x == 0) a.revertWithMessage("expected");
        else b.revertWithMessage("expected");
    }

    function prove_expectPartialRevert_wrong_selector(bool useCustom) public {
        Reverter reverter = new Reverter();
        vm.expectPartialRevert(Reverter.CustomError.selector);
        if (useCustom) reverter.revertWithCustomError();
        else reverter.revertWithMessage("any");
    }

    function prove_expectRevert_only_reverter_mismatch(uint256 x) public {
        Reverter a = new Reverter();
        Reverter b = new Reverter();
        vm.expectRevert(address(a));
        if (x == 0) a.revertWithoutReason();
        else b.revertWithoutReason();
    }

    function prove_expectRevert_wrong_reason_via_error_prefix(uint256 x) public {
        Reverter reverter = new Reverter();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "wrong"));
        if (x == 0) reverter.revertWithMessage("wrong");
        else reverter.revertWithMessage("right");
    }

    function prove_expectRevert_double_set(uint256 x) public {
        if (x == 0) return;
        vm.expectRevert("first");
        vm.expectRevert("second");
    }

    function prove_expectRevert_ok_then_revert(uint256 x) public {
        Reverter reverter = new Reverter();
        if (x == 0) return;
        vm.expectRevert("expected");
        reverter.doNotRevert();
        reverter.revertWithMessage("expected");
    }

    function prove_expectRevert_empty_actual(uint256 x) public {
        Reverter reverter = new Reverter();
        vm.expectRevert("expected");
        if (x == 0) reverter.revertWithMessage("expected");
        else reverter.revertWithoutReason();
    }

    function prove_expectRevert_full_match_extra_args(uint256 x) public {
        WithArgError target = new WithArgError();
        if (x == 0) return;
        vm.expectRevert(abi.encodePacked(WithArgError.CustomError.selector));
        target.go();
    }

    function prove_expectRevert_no_subcall(uint256 x) public {
        if (x == 0) return;
        vm.expectRevert("never happens");
    }

    // The expectation must be consumed by a strict sub-call. The test body's
    // own revert does not satisfy it, even when the reason matches.
    function prove_expectRevert_body_revert_matches(uint256 x) public {
        if (x == 0) return;
        vm.expectRevert("from body");
        require(false, "from body");
    }
}
