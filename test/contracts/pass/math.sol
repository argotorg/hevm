// SPDX-License-Identifier: AGPL-3.0
pragma solidity >=0.8.0 <0.9.0;

/// Adapted from halmos tests/solver/test/Math.t.sol
/// Tests average computation equivalence
contract MathTest {
    function prove_Avg(uint a, uint b) public pure {
        unchecked {
            uint r1 = (a & b) + (a ^ b) / 2;
            uint r2 = (a + b) / 2;
            assert(r1 == r2);
        }
    }
}
