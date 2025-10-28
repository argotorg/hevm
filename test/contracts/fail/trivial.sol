import {Test} from "forge-std/Test.sol";

// should run and fail
contract Trivial is Test {
    function prove_false() public {
        assertTrue(false);
    }
}

