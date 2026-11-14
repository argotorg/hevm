// Runs offline against rpc-cache-16198552.json; regenerate it with a real --rpc and --cache-dir.
// Over 5 calls into one contract on a path trips the default --max-iterations.
pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";

interface WETH9 {
    function balanceOf(address) external view returns (uint256);
    function allowance(address, address) external view returns (uint256);
    function totalSupply() external view returns (uint256);
    function approve(address, uint256) external returns (bool);
    function transfer(address, uint256) external returns (bool);
    function transferFrom(address, address, uint256) external returns (bool);
}

interface UniswapV2Pair {
    function token0() external view returns (address);
    function token1() external view returns (address);
    function getReserves() external view returns (uint112, uint112, uint32);
}

contract RpcCached is Test {
    WETH9 weth = WETH9(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    UniswapV2Pair pair = UniswapV2Pair(0xB4e16d0168e52d35CaCD2c6185b44281Ec28C9Dc);
    address usdc = 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48;
    address holder = 0xF04a5cC80B1E94C69B48f5ee68a08CD2F09A7c3E;
    address dead = address(0xdead);
    uint256 deadBalance = 2595433725034301;

    function prove_concrete_mapping_read() public {
        assertEq(weth.balanceOf(dead), deadBalance);
        assertGt(weth.balanceOf(holder), 0);
    }

    function prove_account_fields() public {
        // WETH9.totalSupply() is this.balance
        assertEq(address(weth).balance, weth.totalSupply());
        assertGt(address(weth).balance, 0);
        assertEq(address(weth).codehash, keccak256(address(weth).code));
        assertEq(address(0xbeef).code.length, 0);
    }

    function prove_transfer_over_fetched_storage(uint256 wad) public {
        uint256 holderBefore = weth.balanceOf(holder);
        vm.assume(wad <= holderBefore);
        vm.prank(holder);
        assertTrue(weth.transfer(dead, wad));
        assertEq(weth.balanceOf(holder), holderBefore - wad);
        assertEq(weth.balanceOf(dead), deadBalance + wad);
    }

    function prove_nested_mapping_allowance(uint256 wad) public {
        vm.assume(wad <= weth.balanceOf(holder) && wad < type(uint256).max);
        vm.prank(holder);
        assertTrue(weth.approve(address(this), wad));
        assertEq(weth.allowance(holder, address(this)), wad);
        assertTrue(weth.transferFrom(holder, dead, wad));
        assertEq(weth.allowance(holder, address(this)), 0);
    }

    function prove_multiple_contracts_and_packed_slot() public {
        assertEq(pair.token0(), usdc);
        assertEq(pair.token1(), address(weth));
        (uint112 r0, uint112 r1, uint32 ts) = pair.getReserves();
        assertGt(r0, 0);
        assertGt(r1, 0);
        assertGt(ts, 0);
        assertLe(r1, weth.balanceOf(address(pair)));
    }

    function prove_fail_overdraft_reverts(uint256 wad) public {
        uint256 bal = weth.balanceOf(holder);
        vm.prank(holder);
        assertTrue(weth.transfer(dead, wad));
        assertLe(wad, bal / 2);
    }
}
