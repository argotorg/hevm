// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Soundness guard: m[i] is never written, so this is falsifiable.
contract ArrayMappingSameSlotFail {
    bool public constant IS_TEST = true;
    mapping(uint256 => uint256) m;

    function prove_array_write_read(uint256 i, uint256 j) public {
        // hevm assumes keccak outputs are at least 256 apart
        if (i >= 256 || i == j) return;
        // element i of an array on the slot of m
        assembly {
            mstore(0, m.slot)
            sstore(add(keccak256(0, 32), i), 3)
        }
        m[j] = 5;
        assert(m[i] == 3);
    }
}
