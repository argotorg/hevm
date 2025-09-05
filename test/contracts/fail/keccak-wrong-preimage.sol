
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;
import {Test} from "forge-std/Test.sol";

contract MyContract is Test {
  mapping (uint => uint) balances;
  function setUp() public {
    balances[0xfaaaaaffafafafafaaaaa472134] = 50;
  }
  function prove_keccak_wrong(uint number) public view {
    bytes32 hash = keccak256(abi.encodePacked(number));
    uint balance = balances[uint(hash)];
    assert(balance != 50);
  }
}
