import "forge-std/Test.sol";

contract AssertApproxEqAbsFailTest is Test {
    // --- uint256 failures ---

    function prove_approx_eq_abs_uint_exceeds_delta() public pure {
        // delta = 11, maxDelta = 10 -> should fail
        assertApproxEqAbs(uint256(111), uint256(100), 10);
    }

    function prove_approx_eq_abs_uint_zero_delta_neq() public pure {
        // exact equality required, but values differ
        assertApproxEqAbs(uint256(1), uint256(0), 0);
    }

    // --- int256 failures ---

    function prove_approx_eq_abs_int_exceeds_delta() public pure {
        // delta(-6, 5) = 6 + 5 = 11, maxDelta = 10 -> should fail
        assertApproxEqAbs(int256(-6), int256(5), 10);
    }

    function prove_approx_eq_abs_int_min_zero_tight() public pure {
        // delta(int256.min, 0) = 2^255, maxDelta = 2^255 - 1 -> should fail
        assertApproxEqAbs(type(int256).min, int256(0), uint256(2**255 - 1));
    }

    // --- symbolic failure ---

    function prove_approx_eq_abs_uint_symbolic_fail(uint256 a) public pure {
        // a vs 0 with delta 0 means a must be 0, but a is unconstrained -> should fail
        assertApproxEqAbs(a, uint256(0), 0);
    }
}
