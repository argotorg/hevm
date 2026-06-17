import "forge-std/Test.sol";

// Passing counterparts of the new message-bearing and bytes assert overloads.
// For most overloads forge-std short-circuits on the passing branch and never
// reaches the cheatcode, so these mainly guard against compile/behaviour
// regressions; the assertApproxEq{Abs,Rel}(...,string) overloads forward to the
// cheatcode unconditionally and therefore exercise hevm's handler here too.
contract AssertMsgPassTest is Test {
    function prove_eq_bool_msg() public pure {
        assertEq(true, true, "bool eq");
    }

    function prove_eq_uint_msg() public pure {
        assertEq(uint256(1), uint256(1), "uint eq");
    }

    function prove_eq_int_msg() public pure {
        assertEq(int256(-1), int256(-1), "int eq");
    }

    function prove_eq_addr_msg() public pure {
        assertEq(address(uint160(1)), address(uint160(1)), "addr eq");
    }

    function prove_eq_bytes32_msg() public pure {
        assertEq(bytes32(uint256(1)), bytes32(uint256(1)), "bytes32 eq");
    }

    function prove_eq_string_msg() public pure {
        assertEq(string("a"), string("a"), "string eq");
    }

    function prove_eq_bytes_msg() public pure {
        assertEq(bytes("a"), bytes("a"), "bytes eq");
    }

    function prove_neq_uint_msg() public pure {
        assertNotEq(uint256(1), uint256(2), "uint neq");
    }

    function prove_neq_string_msg() public pure {
        assertNotEq(string("a"), string("b"), "string neq");
    }

    function prove_neq_bytes_msg() public pure {
        assertNotEq(bytes("a"), bytes("b"), "bytes neq");
    }

    function prove_lt_uint_msg() public pure {
        assertLt(uint256(1), uint256(2), "uint lt");
    }

    function prove_lt_int_msg() public pure {
        assertLt(int256(-1), int256(2), "int lt");
    }

    function prove_le_uint_msg() public pure {
        assertLe(uint256(1), uint256(1), "uint le");
    }

    function prove_gt_uint_msg() public pure {
        assertGt(uint256(2), uint256(1), "uint gt");
    }

    function prove_gt_int_msg() public pure {
        assertGt(int256(2), int256(-1), "int gt");
    }

    function prove_ge_uint_msg() public pure {
        assertGe(uint256(1), uint256(1), "uint ge");
    }

    function prove_approx_abs_uint_msg() public pure {
        assertApproxEqAbs(uint256(10), uint256(10), 0, "abs");
    }

    function prove_approx_rel_uint_msg() public pure {
        assertApproxEqRel(uint256(105), uint256(100), 1e17, "rel");
    }

    function prove_approx_rel_int_msg() public pure {
        assertApproxEqRel(int256(-95), int256(-100), 1e17, "rel int");
    }

    function prove_eq_bytes() public pure {
        assertEq(bytes("a"), bytes("a"));
    }

    function prove_neq_bytes() public pure {
        assertNotEq(bytes("a"), bytes("b"));
    }
}
