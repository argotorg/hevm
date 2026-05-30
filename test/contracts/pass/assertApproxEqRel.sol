import "forge-std/Test.sol";

contract AssertApproxEqRelTest is Test {
    // maxPercentDelta is an 18-decimal fixed point number where 1e18 == 100%.
    // percentDelta = |a - b| * 1e18 / b  (denominator is the second argument)

    // --- uint256 concrete tests ---

    function prove_approx_eq_rel_uint_exact() public pure {
        // pd = 0
        assertApproxEqRel(uint256(100), uint256(100), 0);
    }

    function prove_approx_eq_rel_uint_within_delta() public pure {
        // pd = |105-100| * 1e18 / 100 = 5e16 (5%), max 10%
        assertApproxEqRel(uint256(105), uint256(100), 1e17);
    }

    function prove_approx_eq_rel_uint_at_boundary() public pure {
        // pd = |110-100| * 1e18 / 100 = 1e17 (10%), max 10% -> inclusive pass
        assertApproxEqRel(uint256(110), uint256(100), 1e17);
    }

    function prove_approx_eq_rel_uint_both_zero() public pure {
        // b == 0 && a == 0 -> treated as equal
        assertApproxEqRel(uint256(0), uint256(0), 0);
    }

    function prove_approx_eq_rel_uint_full_delta() public pure {
        // pd = |2-1| * 1e18 / 1 = 1e18 (100%), max 100%
        assertApproxEqRel(uint256(2), uint256(1), 1e18);
    }

    function prove_approx_eq_rel_uint_large_values() public pure {
        // no intermediate overflow despite huge magnitudes (computed in wider precision)
        assertApproxEqRel(type(uint256).max, type(uint256).max, 0);
    }

    // --- int256 concrete tests ---

    function prove_approx_eq_rel_int_exact() public pure {
        assertApproxEqRel(int256(-100), int256(-100), 0);
    }

    function prove_approx_eq_rel_int_same_sign() public pure {
        // same sign: absDelta = |100-95| = 5, denom = |−100| = 100, pd = 5e16 (5%)
        assertApproxEqRel(int256(-95), int256(-100), 1e17);
    }

    function prove_approx_eq_rel_int_opposite_signs() public pure {
        // opposite signs: absDelta = |−5| + |5| = 10, denom = |5| = 5, pd = 2e18 (200%)
        assertApproxEqRel(int256(-5), int256(5), 2e18);
    }

    function prove_approx_eq_rel_int_both_zero() public pure {
        assertApproxEqRel(int256(0), int256(0), 0);
    }

    // --- uint256 symbolic tests ---

    function prove_approx_eq_rel_uint_symbolic(uint256 a) public pure {
        // any value is within 0% of itself (and 0 ~= 0 holds when b == 0)
        assertApproxEqRel(a, a, 0);
    }

    function prove_approx_eq_rel_uint_symbolic_maxdelta(uint256 a) public pure {
        // a vs a is always within any tolerance
        assertApproxEqRel(a, a, type(uint256).max);
    }
}
