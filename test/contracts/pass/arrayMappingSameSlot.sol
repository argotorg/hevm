// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// An array and a mapping on the same slot must not be treated as one store.
contract ArrayMappingSameSlotPass {
    bool public constant IS_TEST = true;
    mapping(uint256 => uint256) m;

    function prove_array_write_not_read(uint256 i, uint256 j, uint256 k) public {
        // hevm assumes keccak outputs are at least 256 apart
        if (i >= 256) return;
        // element i of an array on the slot of m
        assembly {
            mstore(0, m.slot)
            sstore(add(keccak256(0, 32), i), 3)
        }
        m[j] = 5;
        assert(m[k] != 3);
    }
}
