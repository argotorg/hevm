// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Regression tests for #1082: a symbolic-key SLOAD over a ConcreteStore must
// resolve during execution instead of forking on an unresolved read.

contract SymbolicKeyEmptyStore {
    bool public constant IS_TEST = true;
    mapping(uint256 => uint256) s;

    function prove_symbolic_key_empty_store(uint256 x) public view {
        assert(s[x] == 0);
    }
}

// setUp populates one mapping; a symbolic read of the untouched mapping
// filters out all 600 entries (their recorded keccak preimages identify a
// different mapping) and resolves to 0. Without the fix it does not complete.
contract SymbolicKeyFiltered {
    bool public constant IS_TEST = true;
    mapping(uint256 => uint256) populated;
    mapping(uint256 => uint256) untouched;

    function setUp() public {
        for (uint256 i = 0; i < 600; i++) {
            populated[i] = i + 1;
        }
    }

    function prove_symbolic_key_untouched_mapping(uint256 x) public view {
        assert(untouched[x] == 0);
    }
}
