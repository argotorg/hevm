
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";

contract C {
  function f() public pure returns (uint256) {
    return 42;
  }
}
contract T is Test {
  C c = new C();
  function prove_only_deployed_force_addr(address x) pure public {
    uint256 y = C(x).f();
    assert(y != 42);
  }
}
