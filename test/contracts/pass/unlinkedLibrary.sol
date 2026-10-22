import {Test} from "forge-std/Test.sol";

library L {
    function add(uint256 a, uint256 b) external pure returns (uint256) { return a + b; }
}

contract UsesL {
    function f(uint256 x) external pure returns (uint256) { return L.add(x, 1); }
}

contract UnlinkedLibraryTest is Test {
    function prove_unrelated(uint8 x) public pure {
        assertEq(uint256(x) + 1, uint256(x) + 1);
    }
}
