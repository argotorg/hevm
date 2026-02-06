// SPDX-License-Identifier: AGPL-3.0
pragma solidity >=0.8.0 <0.9.0;

import {Test} from "forge-std/Test.sol";

/// Adapted from halmos tests/solver/test/Math.t.sol
/// Deposit/mint ratio test - counterexamples exist for mint case
contract MathFailTest is Test {
    function prove_mint(uint s, uint A1, uint S1) public pure {
        uint a = (s * A1) / S1;

        uint A2 = A1 + a;
        uint S2 = S1 + s;

        // (A1 / S1 <= A2 / S2)
        assert(A1 * S2 <= A2 * S1); // counterexamples exist
    }
}
