// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity ^0.8.18;

import {Test} from "forge-std/Test.sol";

contract Reverter {
    error CustomError();

    function revertWithMessage(string memory message) public pure {
        revert(message);
    }

    function doNotRevert() public pure {}

    function panic() public pure returns (uint256) {
        return uint256(100) - uint256(101);
    }

    function revertWithCustomError() public pure {
        revert CustomError();
    }

    function nestedRevert(Reverter inner, string memory message) public pure {
        inner.revertWithMessage(message);
    }

    function callThenRevert(Dummy dummy, string memory message) public pure {
        dummy.callMe();
        revert(message);
    }

    function revertWithoutReason() public pure {
        revert();
    }
}

contract ConstructorReverter {
    constructor(string memory message) {
        revert(message);
    }
}

contract DelegateLogic {
    function doRevert(string memory m) external pure {
        revert(m);
    }
}

contract DelegateProxy {
    address public logicAddr;
    constructor(address _logic) { logicAddr = _logic; }
    function relay(string memory m) external returns (bytes memory) {
        (bool ok, bytes memory ret) = logicAddr.delegatecall(
            abi.encodeWithSignature("doRevert(string)", m));
        if (!ok) { assembly { revert(add(ret, 0x20), mload(ret)) } }
        return ret;
    }
}

struct LargeDummyStruct {
    address a;
    uint256 b;
    bool c;
    address d;
    address e;
    string f;
    address[8] g;
    address h;
    uint256 i;
}

contract Dummy {
    function callMe() public pure returns (string memory) {
        return "thanks for calling";
    }

    function largeReturnType() public pure returns (LargeDummyStruct memory) {
        revert("reverted with large return type");
    }
}

contract MutatingReverter {
    uint256 public x;
    function setAndRevert(uint256 v, string memory m) external {
        x = v;
        revert(m);
    }
}

contract StorageBox {
    uint256 public x;
    function set(uint256 v) external { x = v; }
}

contract CtorMutatingReverter {
    constructor(StorageBox s, uint256 v) {
        s.set(v);
        revert("ctor revert");
    }
}

contract ExpectRevertTest is Test {
    function prove_expectRevertString() public {
        Reverter reverter = new Reverter();
        vm.expectRevert("revert");
        reverter.revertWithMessage("revert");
    }

    function prove_expectRevertWithEncodedErrorPrefix() public {
        Reverter reverter = new Reverter();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "my revert reason"));
        reverter.revertWithMessage("my revert reason");

        vm.expectRevert(abi.encodeWithSignature("Error(string)", "A"));
        reverter.revertWithMessage("A");

        vm.expectRevert(abi.encodeWithSignature("Error(string)", "revert: A"));
        reverter.revertWithMessage("revert: A");
    }

    function prove_expectRevertConstructor() public {
        vm.expectRevert("constructor revert");
        new ConstructorReverter("constructor revert");
    }

    function prove_expectRevertConstructorReturnsDummyAddress() public {
        vm.expectRevert("constructor revert");
        ConstructorReverter r = new ConstructorReverter("constructor revert");
        require(address(r) == address(0x0000000000000000000000000000000000000001),
                "swallowed CREATE must return DUMMY_CREATE_ADDRESS");
    }

    function prove_expectRevertBuiltin() public {
        Reverter reverter = new Reverter();
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x11));
        reverter.panic();
    }

    function prove_expectRevertCustomError() public {
        Reverter reverter = new Reverter();
        vm.expectRevert(abi.encodePacked(Reverter.CustomError.selector));
        reverter.revertWithCustomError();
    }

    function prove_expectRevertNested() public {
        Reverter reverter = new Reverter();
        Reverter inner = new Reverter();
        vm.expectRevert("nested revert");
        reverter.nestedRevert(inner, "nested revert");
    }

    function prove_expectRevertCallsThenReverts() public {
        Reverter reverter = new Reverter();
        Dummy dummy = new Dummy();
        vm.expectRevert("called a function and then reverted");
        reverter.callThenRevert(dummy, "called a function and then reverted");
    }

    function prove_dummyReturnDataForBigType() public {
        Dummy dummy = new Dummy();
        vm.expectRevert("reverted with large return type");
        dummy.largeReturnType();
    }

    function prove_expectRevertNoReason() public {
        Reverter reverter = new Reverter();
        vm.expectRevert(bytes(""));
        reverter.revertWithoutReason();
    }

    function prove_expectRevertAnyRevert() public {
        vm.expectRevert();
        new ConstructorReverter("hello this is a revert message");

        Reverter reverter = new Reverter();
        vm.expectRevert();
        reverter.revertWithMessage("this is also a revert message");

        vm.expectRevert();
        reverter.panic();

        vm.expectRevert();
        reverter.revertWithCustomError();

        Reverter reverter2 = new Reverter();
        vm.expectRevert();
        reverter.nestedRevert(reverter2, "this too is a revert message");

        Dummy dummy = new Dummy();
        vm.expectRevert();
        reverter.callThenRevert(dummy, "revert message 4 i ran out of synonims for also");

        vm.expectRevert();
        reverter.revertWithoutReason();
    }

    function prove_expectRevertEmptyString() public {
        Reverter reverter = new Reverter();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", ""));
        reverter.revertWithMessage("");
    }

    function prove_expectRevertCreate2Sentinel() public {
        vm.expectRevert("ctor revert");
        ConstructorReverter r = new ConstructorReverter{salt: bytes32(uint256(1))}("ctor revert");
        require(address(r) == address(0x0000000000000000000000000000000000000001),
                "swallowed CREATE2 must return DUMMY_CREATE_ADDRESS");
    }

    function prove_expectRevertSurvivesIntermediateCheat() public {
        Reverter reverter = new Reverter();
        vm.expectRevert("delayed");
        vm.label(address(reverter), "reverter");
        reverter.revertWithMessage("delayed");
    }

    function prove_expectRevertThroughDelegatecall() public {
        DelegateLogic logic = new DelegateLogic();
        DelegateProxy proxy = new DelegateProxy(address(logic));
        vm.expectRevert("logic revert", address(proxy));
        proxy.relay("logic revert");
    }

    function prove_expectRevertCallRollsBackState() public {
        MutatingReverter r = new MutatingReverter();
        require(r.x() == 0, "pre-state must be 0");
        vm.expectRevert("call revert");
        r.setAndRevert(42, "call revert");
        require(r.x() == 0, "swallowed CALL revert must roll back state");
    }

    function prove_expectRevertCreateRollsBackState() public {
        StorageBox s = new StorageBox();
        require(s.x() == 0, "pre-state must be 0");
        vm.expectRevert("ctor revert");
        new CtorMutatingReverter(s, 42);
        require(s.x() == 0, "swallowed CREATE revert must roll back state");
    }
}

contract AContract {
    BContract bContract;
    CContract cContract;

    constructor(BContract _bContract, CContract _cContract) {
        bContract = _bContract;
        cContract = _cContract;
    }

    function callAndRevert() public pure {
        require(1 > 2, "Reverted by AContract");
    }

    function callAndRevertInBContract() public {
        bContract.callAndRevert();
    }

    function callAndRevertInCContract() public {
        cContract.callAndRevert();
    }

    function callAndRevertInCContractThroughBContract() public {
        bContract.callAndRevertInCContract();
    }

    function createDContract() public {
        new DContract();
    }

    function createDContractThroughBContract() public {
        bContract.createDContract();
    }

    function createDContractThroughCContract() public {
        cContract.createDContract();
    }

    function doNotRevert() public {}
}

contract BContract {
    CContract cContract;

    constructor(CContract _cContract) {
        cContract = _cContract;
    }

    function callAndRevert() public pure {
        require(1 > 2, "Reverted by BContract");
    }

    function callAndRevertInCContract() public {
        this.doNotRevert();
        cContract.doNotRevert();
        cContract.callAndRevert();
    }

    function createDContract() public {
        this.doNotRevert();
        cContract.doNotRevert();
        new DContract();
    }

    function createDContractThroughCContract() public {
        this.doNotRevert();
        cContract.doNotRevert();
        cContract.createDContract();
    }

    function doNotRevert() public {}
}

contract CContract {
    error CContractError(string reason);

    function callAndRevert() public pure {
        revert CContractError("Reverted by CContract");
    }

    function createDContract() public {
        new DContract();
    }

    function doNotRevert() public {}
}

contract DContract {
    constructor() {
        require(1 > 2, "Reverted by DContract");
    }
}

contract ExpectRevertWithReverterTest is Test {
    error CContractError(string reason);

    AContract aContract;
    BContract bContract;
    CContract cContract;

    function setUp() public {
        cContract = new CContract();
        bContract = new BContract(cContract);
        aContract = new AContract(bContract, cContract);
    }

    function prove_expectRevertsWithReverter() public {
        vm.expectRevert(address(aContract));
        aContract.callAndRevert();

        vm.expectRevert(address(bContract));
        aContract.callAndRevertInBContract();

        vm.expectPartialRevert(CContractError.selector, address(cContract));
        aContract.callAndRevertInCContractThroughBContract();

        vm.expectRevert(abi.encodeWithSelector(CContractError.selector, "Reverted by CContract"), address(cContract));
        aContract.callAndRevertInCContract();
    }

    function prove_expectRevertsWithReverterInConstructor() public {
        vm.expectRevert(abi.encodePacked("Reverted by DContract"), address(cContract));
        cContract.createDContract();

        vm.expectRevert(address(bContract));
        bContract.createDContract();
        vm.expectRevert(address(cContract));
        bContract.createDContractThroughCContract();

        vm.expectRevert(address(aContract));
        aContract.createDContract();
        vm.expectRevert(address(bContract));
        aContract.createDContractThroughBContract();
        vm.expectRevert(address(cContract));
        aContract.createDContractThroughCContract();
    }
}
