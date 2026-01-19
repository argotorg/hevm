/// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.26;
import {Test} from "forge-std/Test.sol";

contract MyVault {
    mapping(address => uint256) public balance;
    function deposit() external payable {
        balance[msg.sender] += msg.value;
    }
}

contract Caller {}

contract SymbolicTest is Test {
    function setUp() public {
        address caller = address(0xdead);
        vm.startPrank(caller);
        new MyVault();
        new MyVault();
    }

    function prove_nonce_addr_nonexistent(uint8 amt) public {
        assert(1 == 1);
      }
}

contract SymbolicTest2 is Test {
    function setUp() public {
        address caller = address(new Caller());
        // option 2
        // address caller = makeAddr("alice");
        vm.deal(caller, 1 ether); // just in case...
        vm.startPrank(caller);
        new MyVault();
        new MyVault();
    }

    function prove_prank_addr_exists(uint8 amt) public {
        assert(1 == 1);
      }
}
