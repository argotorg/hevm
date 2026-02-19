import "forge-std/Test.sol";
import "tokens/erc20.sol";

contract C is Test {
  function prove_f(uint256 x) public pure {
    unchecked {
    uint256 result = 1;
    if (x & 0x1 != 0) result = result * 2;
    if (x & 0x2 != 0) result = result * 3;
    if (x & 0x4 != 0) result = result * 6;
    if (x & 0x8 != 0) result = result * 8;
    assert(result > 1);
    }
  }
}
