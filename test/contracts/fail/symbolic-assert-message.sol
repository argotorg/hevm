pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";

contract SymbolicAssertMessage is Test {
    function prove_le(uint256 x) public pure {
        vm.assume(x > 997 && x < 999);
        assertLe(x * 3, 2000);
    }
}
