// SPDX-License-Identifier: MIT
pragma solidity ^0.8.31;

import "forge-std/Test.sol";

contract FusakaTests is Test {
    // Test CLZ (Count Leading Zeros) opcode (0x1e)
    // Using Yul assembly with osaka EVM version

    function clz_test(uint256 x) internal pure returns (uint256 result) {
        assembly {
            result := clz(x)
        }
    }

    // CLZ of 0 should return 256
    function check_clz_zero() public {
        assertEq(clz_test(0), 256);
    }

    // CLZ of 1 should return 255 (only bit 0 is set)
    function check_clz_one() public {
        assertEq(clz_test(1), 255);
    }

    // CLZ of max uint256 should return 0 (bit 255 is set)
    function check_clz_max() public {
        assertEq(clz_test(type(uint256).max), 0);
    }

    // CLZ of 0x8000...0000 (1 << 255) should return 0
    function check_clz_msb_set() public {
        assertEq(clz_test(1 << 255), 0);
    }

    // CLZ of 0x4000...0000 (1 << 254) should return 1
    function check_clz_bit254() public {
        assertEq(clz_test(1 << 254), 1);
    }

    // CLZ of 0x100 (1 << 8) should return 247
    function check_clz_bit8() public {
        assertEq(clz_test(1 << 8), 247);
    }

    // CLZ of 0xFF should return 248 (bits 0-7 set, MSB at bit 7)
    function check_clz_0xff() public {
        assertEq(clz_test(0xFF), 248);
    }

    // CLZ of 0x80 (1 << 7) should return 248
    function check_clz_bit7() public {
        assertEq(clz_test(0x80), 248);
    }
}
