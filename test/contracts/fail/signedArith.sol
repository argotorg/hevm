// SPDX-License-Identifier: AGPL-3.0
pragma solidity >=0.8.0 <0.9.0;

import "forge-std/Test.sol";

/// Adapted from halmos tests/solver/test/SignedDiv.t.sol
/// Tests signed wadMul edge case (bad implementation - should find counterexample)
/// Counterexample: x = -1, y = type(int256).min

interface WadMul {
    function wadMul(int256 x, int256 y) external pure returns (int256);
}

contract SolmateBadWadMul is WadMul {
    function wadMul(int256 x, int256 y) public pure override returns (int256 r) {
        assembly {
            r := mul(x, y)
            if iszero(or(iszero(x), eq(sdiv(r, x), y))) { revert(0, 0) }
            r := sdiv(r, 1000000000000000000)
        }
    }
}

contract SolidityWadMul is WadMul {
    function wadMul(int256 x, int256 y) public pure override returns (int256) {
        return (x * y) / 1e18;
    }
}

contract TestBadWadMul is Test {
    WadMul wadMulImpl;
    SolidityWadMul solidityWadMul;

    function setUp() public {
        wadMulImpl = new SolmateBadWadMul();
        solidityWadMul = new SolidityWadMul();
    }

    function prove_wadMul_solEquivalent(int256 x, int256 y) external {
        bytes memory encodedCall = abi.encodeWithSelector(WadMul.wadMul.selector, x, y);

        (bool succ1, bytes memory retbytes1) = address(solidityWadMul).call(encodedCall);
        (bool succ2, bytes memory retbytes2) = address(wadMulImpl).call(encodedCall);

        assertEq(succ1, succ2);

        if (succ1 && succ2) {
            int256 result1 = abi.decode(retbytes1, (int256));
            int256 result2 = abi.decode(retbytes2, (int256));
            assertEq(result1, result2);
        }
    }
}
