// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.0;

import {Test} from "forge-std/Test.sol";

contract MiniScaler {
    mapping(address => uint256) public bal;

    function scaledConst(address a) external view returns (uint256) {
        return (bal[a] * 1e27) / 1e27;
    }
}

/// Regression for keeping abstract-arithmetic lemmas aligned with the terms in
/// the asserted goal. Requires `abstractArith = True` in hevm's test config.
contract AbstractArithStorageTest is Test {
    MiniScaler internal m;
    address internal constant HOLDER = address(0x1234);

    function setUp() public {
        m = new MiniScaler();
    }

    /// A concrete mapping slot holds a symbolic value. Simplification resolves
    /// the goal's read to that value; lemmas generated from the raw props retain
    /// a select over the whole storage array and cannot prove the equality.
    function check_constCancelConcreteKey(uint256 v) external {
        vm.assume(v < 2 ** 128);
        vm.store(address(m), keccak256(abi.encode(HOLDER, uint256(0))), bytes32(v));
        assertEq(m.scaledConst(HOLDER), v, "constCancelConcreteKey");
    }
}
