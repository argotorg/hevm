// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.17;

contract MappingAliasTest {
    // HEVM test discovery marker; constant so it occupies no storage slot.
    bool public constant IS_TEST = true;

    mapping(uint256 => uint256) private written;
    mapping(uint256 => uint256) private unwritten;

    function test_unwritten(uint256 key) public {
        written[1] = 3;
        assert(unwritten[key] == 0);
    }
}

contract MappingFalseProofTest {
    bool public constant IS_TEST = true;

    mapping(uint256 => uint256) private written;

    // Deliberately false at key = 1: HEVM must find that counterexample.
    function test_written_is_zero(uint256 key) public {
        written[1] = 3;
        assert(written[key] == 0);
    }
}
