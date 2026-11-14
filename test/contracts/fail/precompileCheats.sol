import {Test} from "forge-std/Test.sol";

contract C {
    function who() external view returns (address) { return msg.sender; }
    function bad() external pure { revert("boom"); }
}

contract PrecompileCheatsTest is Test {
    function prove_prank_not_kept_past_precompile() public {
        C c = new C();
        vm.prank(address(0xBEEF));
        ecrecover(bytes32(uint256(1)), 27, bytes32(uint256(1)), bytes32(uint256(1)));
        assertEq(c.who(), address(0xBEEF));
    }

    function prove_expectRevert_on_succeeding_precompile() public {
        C c = new C();
        vm.expectRevert();
        ecrecover(bytes32(uint256(1)), 27, bytes32(uint256(1)), bytes32(uint256(1)));
        c.bad();
    }
}
