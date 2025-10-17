pragma solidity ^0.8.20;

contract KeccakTest {
  bool public IS_TEST = true;
  mapping(int24 => uint256) private tickBitmap;

  int24[] initedTicks;

  constructor() public {
    initedTicks.push(1);
  }

  function prove_access(int24 tick) public view {
    assert(tickBitmap[tick] == 0);
  }
}
