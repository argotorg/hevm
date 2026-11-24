// Verified contracts to try, with tests of them in place of the starter test.

export interface SourcifyExample {
  name: string;
  chainId: string;
  address: string;
  testPath: string;
  test: string;
}

export const sourcifyExamples: SourcifyExample[] = [
  {
    name: "Uniswap V3 Factory",
    chainId: "1",
    address: "0x1F98431c8aD98523631AE4a59f267346ea31F984",
    testPath: "test/UniswapV3Factory.t.sol",
    test: `// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.7.0;

import {Test} from "hevm/Test.sol";
import {UniswapV3Factory} from "contracts/UniswapV3Factory.sol";
import {IUniswapV3Pool} from "contracts/interfaces/IUniswapV3Pool.sol";

// Properties of Uniswap V3's factory, which hevm proves for all their arguments.
// The test contract deploys the factory, so it is the factory's owner.
contract UniswapV3FactoryTest is Test {
    UniswapV3Factory factory;
    address constant tokenA = address(0x1000);
    address constant tokenB = address(0x2000);

    function setUp() public {
        factory = new UniswapV3Factory();
    }

    // it starts with three fee tiers, 0.05%, 0.3% and 1%, and no other fee has one
    function prove_initial_fee_tiers(uint24 fee) public view {
        int24 spacing = factory.feeAmountTickSpacing(fee);
        if (fee == 500) assert(spacing == 10);
        else if (fee == 3000) assert(spacing == 60);
        else if (fee == 10000) assert(spacing == 200);
        else assert(spacing == 0);
    }

    // a fee tier the owner adds has the tick spacing asked for
    function prove_enable_fee(uint24 fee, int24 spacing) public {
        factory.enableFeeAmount(fee, spacing);
        assert(factory.feeAmountTickSpacing(fee) == spacing);
    }

    // this one fails: hevm finds a fee tier that enableFeeAmount turns down
    function prove_enable_fee_never_reverts(uint24 fee, int24 spacing) public {
        try factory.enableFeeAmount(fee, spacing) {} catch {
            assert(false);
        }
    }

    // a pool is found whichever order its tokens are given in, and keeps them sorted
    function prove_create_pool() public {
        address pool = factory.createPool(tokenB, tokenA, 3000);
        assert(factory.getPool(tokenA, tokenB, 3000) == pool);
        assert(factory.getPool(tokenB, tokenA, 3000) == pool);
        assert(IUniswapV3Pool(pool).token0() == tokenA);
        assert(IUniswapV3Pool(pool).fee() == 3000);
    }

    // there is one pool per pair of tokens and fee tier
    function prove_one_pool_per_pair() public {
        factory.createPool(tokenA, tokenB, 500);
        try factory.createPool(tokenB, tokenA, 500) {
            assert(false);
        } catch {}
    }
}
`,
  },
];

export function sourcifyExample(chainId: string, address: string): SourcifyExample | undefined {
  return sourcifyExamples.find((e) => e.chainId === chainId && e.address.toLowerCase() === address.toLowerCase());
}
