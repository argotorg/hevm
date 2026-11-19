import {Test} from "forge-std/Test.sol";

contract NonUtf8Cex is Test {
  function prove_bytes(bytes2 b) public pure {
    assert(b != "hi");
  }
}
