import "forge-std/Test.sol";

contract PanicTest is Test {
    function prove_panic() public {
        Panicker p = new Panicker();
        p.doPanic();
        assert(true);
    }
}

contract Panicker {
    function doPanic() public pure {
        assert(false);
    }
}
