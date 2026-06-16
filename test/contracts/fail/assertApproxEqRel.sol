import "forge-std/Test.sol";

contract AssertApproxEqRelFailTest is Test {
    // percentDelta = |a - b| * 1e18 / b  (denominator is the second argument)

    // --- uint256 failures ---

    function prove_approx_eq_rel_uint_exceeds_delta() public pure {
        // pd = |111-100| * 1e18 / 100 = 1.1e17 (11%), max 10% -> should fail
        assertApproxEqRel(uint256(111), uint256(100), 1e17);
    }

    function prove_approx_eq_rel_uint_b_zero_neq() public pure {
        // b == 0 but a != 0 -> real delta undefined -> should fail
        assertApproxEqRel(uint256(1), uint256(0), 0);
    }

    function prove_approx_eq_rel_uint_overflow_delta() public pure {
        // huge difference: absDelta ~ 2^256, denom = 1, so percentDelta ~ 2^256 * 1e18
        // does not fit in uint256 -> "overflow in delta calculation" -> should fail
        // even with the maximum tolerance.
        assertApproxEqRel(type(uint256).max, uint256(1), type(uint256).max);
    }

    // --- int256 failures ---

    function prove_approx_eq_rel_int_exceeds_delta() public pure {
        // opposite signs: absDelta = |−6| + |5| = 11, denom = |5| = 5, pd = 2.2e18 (220%), max 100% -> fail
        assertApproxEqRel(int256(-6), int256(5), 1e18);
    }

    function prove_approx_eq_rel_int_b_zero_neq() public pure {
        // b == 0 but a != 0 -> should fail
        assertApproxEqRel(int256(5), int256(0), 0);
    }

    // --- symbolic failure ---

    function prove_approx_eq_rel_uint_symbolic_fail(uint256 a) public pure {
        // a vs 100 with 0% tolerance means a must be 100, but a is unconstrained -> should fail
        assertApproxEqRel(a, uint256(100), 0);
    }
}
