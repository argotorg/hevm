// SPDX-License-Identifier: AGPL-3.0
pragma solidity >=0.8.0 <0.9.0;

import "forge-std/Test.sol";

// from halmos: tests/regression/test/Invariant.t.sol, TStore.t.sol, with Clones.clone inlined

contract C {
    uint public num;

    function inc(uint x) public {
        require(x <= 2);
        num += x;
    }
}


contract InvariantTest is Test {
    C c;

    function setUp() public {
        c = new C();
    }

    function invariant_1() public {
        console.log(c.num());
        assertLe(c.num(), 4);
    }

    function invariant_2() public {
        assert(c.num() != 3);
    }
}

// OpenZeppelin's Clones.clone (v5), an EIP-1167 minimal proxy
function clone(address implementation) returns (address instance) {
    assembly {
        mstore(0x00, or(shr(0xe8, shl(0x60, implementation)), 0x3d602d80600a3d3981f3363d3d373d3d3d363d73000000))
        mstore(0x20, or(shl(0x78, implementation), 0x5af43d82803e903d91602b57fd5bf3))
        instance := create(0, 0x09, 0x37)
    }
    require(instance != address(0));
}

contract InvariantProxyTest is Test {
    C impl = new C();
    C c;

    function setUp() public {
        c = C(clone(address(impl)));
    }

    function invariant_proxy_1() public {
        console.log(c.num());
    }

    function invariant_proxy_2() public {
        assert(c.num() != 3);
    }
}

contract T {
    uint public slot0;

    function sstore(uint slot, uint value) public {
        assembly {
            sstore(slot, value)
        }
    }

    function sload(uint slot) public returns (uint value) {
        assembly {
            value := sload(slot)
        }
    }

    function tstore(uint slot, uint value) public {
        assembly {
            tstore(slot, value)
        }
    }

    function tload(uint slot) public returns (uint value) {
        assembly {
            value := tload(slot)
        }
    }
}

/// @custom:halmos --storage-layout generic
contract TStoreTest is Test {
    T c;

    function setUp() public {
        c = new T();
    }

    function check_sload() public {
        assertEq(c.sload(0), 0);
    }

    function check_tload() public {
        assertEq(c.tload(0), 0);
    }

    function check_sstore(uint x) public {
        c.sstore(0, x);
        assertEq(c.sload(0), x);
        assertEq(c.slot0(), x);

        // transient storage isn't affected
        assertEq(c.tload(0), 0);
    }

    function check_tstore(uint x) public {
        c.tstore(0, x);
        assertEq(c.tload(0), x);

        // persistent storage isn't affected
        assertEq(c.slot0(), 0);
        assertEq(c.sload(0), 0);
    }

    function invariant_storage() public {
        assertEq(c.sload(0), 0); // fail
    }

    function invariant_transient_storage() public {
        // note: transient storage is reset after each tx in the invariant tx sequence
        assertEq(c.tload(0), 0); // pass
    }
}
