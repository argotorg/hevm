// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract KeccakLiteralSlotPass {
    bool public constant IS_TEST = true;
    mapping(bytes32 => uint256) a;
    mapping(bytes32 => uint256) b;

    function prove_other_mapping(bytes32 k) public {
        // a[3] = 2, using a compiler-folded mapping slot.
        assembly { sstore(0x101e368776582e57ab3d116ffe2517c0a585cd5b23174b01e275c2d8329c3d83, 2) }
        assert(b[k] == 0);
    }
}
