// SPDX-License-Identifier: AGPL-3.0
pragma solidity >=0.8.0 <0.9.0;

import {Test} from "forge-std/Test.sol";

/// Adapted from halmos tests/regression/test/Arith.t.sol
/// Division failure case: y == 0 is a valid counterexample
contract ArithFailTest is Test {
    function unchecked_div(uint x, uint y) public pure returns (uint ret) {
        assembly {
            ret := div(x, y)
        }
    }

    function prove_Div_fail(uint x, uint y) public pure {
        require(x > y);

        uint q = unchecked_div(x, y);

        // note: since x > y, q can be zero only when y == 0,
        // due to the division-by-zero semantics in the EVM
        assert(q != 0); // counterexample: y == 0
    }
}
