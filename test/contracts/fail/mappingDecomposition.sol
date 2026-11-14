// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Soundness guard: falsifiable at key = 1.
contract MappingDecompositionFail {
    bool public constant IS_TEST = true;
    mapping(uint256 => uint256) written;

    function prove_written_is_zero(uint256 key) public {
        written[1] = 3;
        assert(written[key] == 0);
    }
}
