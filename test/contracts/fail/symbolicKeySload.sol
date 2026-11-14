// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// #1082 soundness guard: entries of the mapping being read must be kept,
// so this assert is falsifiable (e.g. populated[0] = 1).
contract SymbolicKeySloadFail {
    bool public constant IS_TEST = true;
    mapping(uint256 => uint256) populated;

    function setUp() public {
        for (uint256 i = 0; i < 10; i++) {
            populated[i] = i + 1;
        }
    }

    function prove_same_mapping_falsifiable(uint256 x) public view {
        assert(populated[x] == 0);
    }
}
