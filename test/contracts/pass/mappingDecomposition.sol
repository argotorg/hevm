// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// A write to one mapping must not alias a symbolic-key read of another.
contract MappingDecompositionPass {
    bool public constant IS_TEST = true;
    mapping(uint256 => uint256) written;
    mapping(uint256 => uint256) unwritten;

    function prove_unwritten(uint256 key) public {
        written[1] = 3;
        assert(unwritten[key] == 0);
    }
}
