// SPDX-License-Identifier: AGPL-3.0
pragma solidity ^0.8.19;

import "forge-std/Test.sol";

// as the Parity multisig of 2017: the wallet forwards what it does not know to its library
contract WalletLib {
    address public owner;

    function initWallet(address o) public {
        owner = o;
    }

    function setOwner(address o) public {
        require(msg.sender == owner);
        owner = o;
    }
}

contract Wallet {
    address public owner;
    address immutable lib;

    constructor(address l, address o) {
        lib = l;
        owner = o;
    }

    fallback() external {
        (bool ok,) = lib.delegatecall(msg.data);
        require(ok);
    }
}

contract Lib2 {
    function noop() public {}
}

abstract contract WalletTest is Test {
    Wallet wallet;

    function setUp() public virtual {
        wallet = new Wallet(address(new WalletLib()), address(0xbeef));
        targetContract(address(wallet));
        targetSender(address(0xbad));
    }

    function invariant_owner() public view {
        assert(wallet.owner() == address(0xbeef));
    }
}

// without an interface, the wallet has no function to call
contract InvariantNoInterfaceTest is WalletTest {}

contract InvariantInterfaceTest is WalletTest {
    function setUp() public virtual override {
        super.setUp();
        string[] memory names = new string[](1);
        names[0] = "WalletLib";
        targetInterface(FuzzInterface({addr: address(wallet), artifacts: names}));
    }
}

contract InvariantInterfaceSelectorTest is InvariantInterfaceTest {
    function setUp() public override {
        super.setUp();
        bytes4[] memory selectors = new bytes4[](1);
        selectors[0] = WalletLib.setOwner.selector;
        targetSelector(FuzzSelector({addr: address(wallet), selectors: selectors}));
    }
}

contract InvariantInterfacePathTest is WalletTest {
    function setUp() public override {
        super.setUp();
        string[] memory names = new string[](2);
        names[0] = "Lib2";
        names[1] = "src/unit-tests.t.sol:WalletLib";
        targetInterface(FuzzInterface({addr: address(wallet), artifacts: names}));
    }
}

contract InvariantInterfaceUnknownTest is WalletTest {
    function setUp() public override {
        super.setUp();
        string[] memory names = new string[](1);
        names[0] = "NoSuchContract";
        targetInterface(FuzzInterface({addr: address(wallet), artifacts: names}));
    }
}
