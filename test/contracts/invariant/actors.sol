// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import {Test} from "forge-std/Test.sol";

contract Box {
    address public last;

    function touch() public {
        last = msg.sender;
    }
}

// picks the caller from a list by a symbolic index, as invariant handlers do
contract Handler is Test {
    Box public box;
    address[] public actors;

    constructor(Box b) {
        box = b;
        actors.push(address(0x1001));
        actors.push(address(0x1002));
        actors.push(address(0x1003));
    }

    function act(uint256 seed) public {
        vm.prank(actors[seed % actors.length]);
        box.touch();
    }

    function startAct(uint256 seed) public {
        vm.startPrank(actors[seed % actors.length]);
        box.touch();
        vm.stopPrank();
    }
}

contract ActorsTest is Test {
    Box box;
    Handler handler;

    function setUp() public {
        box = new Box();
        handler = new Handler(box);
        targetContract(address(handler));
    }

    function invariant_actor_from_list() public view {
        address l = box.last();
        assertTrue(l == address(0) || l == address(0x1001) || l == address(0x1002) || l == address(0x1003));
    }

    function invariant_not_third_actor() public view {
        assertTrue(box.last() != address(0x1003));
    }
}

// an address from a symbolic string can't be derived, so the call is only partially explored
contract NamedHandler is Test {
    Box public box;

    constructor(Box b) {
        box = b;
    }

    function act(string memory name) public {
        vm.prank(makeAddr(name));
        box.touch();
    }
}

contract NamedActorsTest is Test {
    Box box;

    function setUp() public {
        box = new Box();
        targetContract(address(new NamedHandler(box)));
    }

    function invariant_named() public view {
        assertTrue(box.last() == address(0) || box.last() != address(0));
    }
}
