// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract RecordedPreimageLoop {
    bool public constant IS_TEST = true;
    mapping(uint256 => uint256) a;

    function setUp() public {
        // the key occurs only in the keccak preimage recorded while setUp runs
        a[uint256(keccak256("hevm"))] = 100;
    }

    function prove_loop_bound_from_other_key(uint256 k) public {
        require(k < 1000);
        uint256 n = a[k];
        uint256 c;
        for (uint256 i = 0; i < n; i++) c++;
        assert(c == 0);
    }
}
