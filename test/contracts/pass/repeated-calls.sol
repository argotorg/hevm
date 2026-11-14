pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";

contract B { mapping(address => uint) public balanceOf; }

contract RepeatedCalls is Test {
    B b;
    address d = address(0xdead);
    function setUp() public { b = new B(); }

    // more calls into B than --max-iterations: none of them is a loop iteration
    function prove_seven_calls(uint wad) public {
        vm.assume(wad < 10);
        uint s = wad;
        s += b.balanceOf(d); s += b.balanceOf(d); s += b.balanceOf(d);
        s += b.balanceOf(d); s += b.balanceOf(d); s += b.balanceOf(d);
        s += b.balanceOf(d);
        assertGe(s, wad);
    }
}
