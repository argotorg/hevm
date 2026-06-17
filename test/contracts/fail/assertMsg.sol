import "forge-std/Test.sol";

// Each method violates one of the new message-bearing (`...,string`) assert
// overloads, or one of the new bytes overloads. forge-std only forwards to the
// `vm` cheatcode on the failing branch, so a violation is what actually drives
// hevm's handler (withMsg / keepHeadWords / assertEqMsgDyn). A broken decode
// would surface as a BadCheatCode error instead of a clean assertion failure.
contract AssertMsgFailTest is Test {
    // --- assertEq(...,string): static operands (withMsg) ---

    function prove_eq_bool_msg() public pure {
        assertEq(true, false, "bool eq");
    }

    function prove_eq_uint_msg() public pure {
        assertEq(uint256(1), uint256(2), "uint eq");
    }

    function prove_eq_int_msg() public pure {
        assertEq(int256(-1), int256(2), "int eq");
    }

    function prove_eq_addr_msg() public pure {
        assertEq(address(uint160(1)), address(uint160(2)), "addr eq");
    }

    function prove_eq_bytes32_msg() public pure {
        assertEq(bytes32(uint256(1)), bytes32(uint256(2)), "bytes32 eq");
    }

    // --- assertEq(...,string): dynamic operands (assertEqMsgDyn) ---

    function prove_eq_string_msg() public pure {
        assertEq(string("a"), string("b"), "string eq");
    }

    function prove_eq_bytes_msg() public pure {
        assertEq(bytes("a"), bytes("b"), "bytes eq");
    }

    // --- assertNotEq(...,string) ---

    function prove_neq_uint_msg() public pure {
        assertNotEq(uint256(1), uint256(1), "uint neq");
    }

    function prove_neq_string_msg() public pure {
        assertNotEq(string("a"), string("a"), "string neq");
    }

    function prove_neq_bytes_msg() public pure {
        assertNotEq(bytes("a"), bytes("a"), "bytes neq");
    }

    // --- assert{Lt,Le,Gt,Ge}(...,string) ---

    function prove_lt_uint_msg() public pure {
        assertLt(uint256(2), uint256(1), "uint lt");
    }

    function prove_lt_int_msg() public pure {
        assertLt(int256(2), int256(-1), "int lt");
    }

    function prove_le_uint_msg() public pure {
        assertLe(uint256(2), uint256(1), "uint le");
    }

    function prove_gt_uint_msg() public pure {
        assertGt(uint256(1), uint256(2), "uint gt");
    }

    function prove_gt_int_msg() public pure {
        assertGt(int256(-1), int256(2), "int gt");
    }

    function prove_ge_uint_msg() public pure {
        assertGe(uint256(1), uint256(2), "uint ge");
    }

    // --- assertApproxEq{Abs,Rel}(...,string) (vm called unconditionally) ---

    function prove_approx_abs_uint_msg() public pure {
        assertApproxEqAbs(uint256(10), uint256(1), 0, "abs");
    }

    function prove_approx_rel_uint_msg() public pure {
        // pd = |2-1| * 1e18 / 1 = 1e18 (100%) > 0 -> fail
        assertApproxEqRel(uint256(2), uint256(1), 0, "rel");
    }

    function prove_approx_rel_int_msg() public pure {
        assertApproxEqRel(int256(2), int256(1), 0, "rel int");
    }

    // --- new bytes overloads without a message ---

    function prove_eq_bytes() public pure {
        assertEq(bytes("a"), bytes("b"));
    }

    function prove_neq_bytes() public pure {
        assertNotEq(bytes("a"), bytes("a"));
    }
}
