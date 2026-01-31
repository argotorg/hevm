// SPDX-License-Identifier: AGPL-3.0
pragma solidity >=0.8.0 <0.9.0;

import {Test} from "forge-std/Test.sol";

/// Adapted from halmos tests/solver/test/Math.t.sol
/// Tests average computation equivalence
contract MathTest is Test {
    function prove_Avg(uint a, uint b) public pure {
        require(a + b >= a); // no overflow
        unchecked {
            uint r1 = (a & b) + (a ^ b) / 2;
            uint r2 = (a + b) / 2;
            assert(r1 == r2);
        }
    }
}
