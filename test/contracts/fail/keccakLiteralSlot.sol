// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract KeccakLiteralSlotFail {
    bool public constant IS_TEST = true;
    mapping(bytes32 => uint256) a;

    function prove_same_mapping(bytes32 k) public {
        // a[3] = 2: the assertion must fail at k = 3.
        assembly { sstore(0x101e368776582e57ab3d116ffe2517c0a585cd5b23174b01e275c2d8329c3d83, 2) }
        assert(a[k] == 0);
    }
}
