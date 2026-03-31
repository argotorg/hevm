import "forge-std/Test.sol";

contract AssertApproxEqAbsTest is Test {
    // --- uint256 concrete tests ---

    function prove_approx_eq_abs_uint_exact() public pure {
        assertApproxEqAbs(uint256(100), uint256(100), 0);
    }

    function prove_approx_eq_abs_uint_within_delta() public pure {
        assertApproxEqAbs(uint256(105), uint256(100), 10);
    }

    function prove_approx_eq_abs_uint_at_boundary() public pure {
        assertApproxEqAbs(uint256(110), uint256(100), 10);
    }

    function prove_approx_eq_abs_uint_reversed() public pure {
        // order shouldn't matter
        assertApproxEqAbs(uint256(100), uint256(110), 10);
    }

    function prove_approx_eq_abs_uint_zero() public pure {
        assertApproxEqAbs(uint256(0), uint256(0), 0);
    }

    function prove_approx_eq_abs_uint_large_delta() public pure {
        assertApproxEqAbs(uint256(0), type(uint256).max, type(uint256).max);
    }

    // --- int256 concrete tests ---

    function prove_approx_eq_abs_int_exact() public pure {
        assertApproxEqAbs(int256(100), int256(100), 0);
    }

    function prove_approx_eq_abs_int_within_delta() public pure {
        assertApproxEqAbs(int256(-5), int256(3), 10);
    }

    function prove_approx_eq_abs_int_opposite_signs() public pure {
        // delta(-5, 5) = |-5| + |5| = 10
        assertApproxEqAbs(int256(-5), int256(5), 10);
    }

    function prove_approx_eq_abs_int_both_negative() public pure {
        // delta(-100, -95) = 5
        assertApproxEqAbs(int256(-100), int256(-95), 5);
    }

    function prove_approx_eq_abs_int_min_max() public pure {
        // delta(int256.min, int256.max) = 2^255 + (2^255 - 1) = 2^256 - 1 = type(uint256).max
        assertApproxEqAbs(type(int256).min, type(int256).max, type(uint256).max);
    }

    function prove_approx_eq_abs_int_min_zero() public pure {
        // delta(int256.min, 0) = |int256.min| = 2^255
        assertApproxEqAbs(type(int256).min, int256(0), uint256(2**255));
    }

    function prove_approx_eq_abs_int_zero() public pure {
        assertApproxEqAbs(int256(0), int256(0), 0);
    }

    // --- uint256 symbolic tests ---

    function prove_approx_eq_abs_uint_symbolic(uint256 a) public pure {
        // any value is within max delta of itself
        assertApproxEqAbs(a, a, 0);
    }

    function prove_approx_eq_abs_uint_symbolic_maxdelta(uint256 a, uint256 b) public pure {
        // any two uint256 values are within type(uint256).max of each other
        assertApproxEqAbs(a, b, type(uint256).max);
    }
}
