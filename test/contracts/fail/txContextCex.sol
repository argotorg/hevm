import {Test} from "forge-std/Test.sol";

contract TxContextCexTest is Test {
    function prove_origin() public view {
        assert(tx.origin != address(0x1234));
    }

    function prove_coinbase() public view {
        assert(block.coinbase != address(0x1234));
    }
}
