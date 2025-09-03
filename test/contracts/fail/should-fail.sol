
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";

contract MyContract is Test {
  mapping (address => uint) balances;
  function proveFail_single_fail(uint amt) public {
    assertEq(amt, 100);
  }
}
