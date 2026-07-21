pragma experimental ABIEncoderV2;

import "forge-std/Test.sol";

interface Hevm {
    function warp(uint256) external;
    function deal(address,uint256) external;
    function assume(bool) external;
    function roll(uint256) external;
    function load(address,bytes32) external returns (bytes32);
    function store(address,bytes32,bytes32) external;
    function sign(uint256,bytes32) external returns (uint8,bytes32,bytes32);
    function addr(uint256) external returns (address);
    function ffi(string[] calldata) external returns (bytes memory);
    function prank(address) external;
    function startPrank(address) external;
    function stopPrank() external;
    function label(address addr, string calldata label) external;
    function setEnv(string calldata variable, string calldata value) external;
    function envBool(string calldata key) external returns (bool);
    function envBool(string calldata key, string calldata delimiter) external returns (bool[] memory);
    function envUint(string calldata key) external returns (uint256 value);
    function envUint(string calldata key, string calldata delimiter) external returns (uint256[] memory values);
    function envInt(string calldata key) external returns (int256 value);
    function envInt(string calldata key, string calldata delimiter) external returns (int256[] memory values);
    function envAddress(string calldata key) external returns (address value);
    function envAddress(string calldata key, string calldata delimiter) external returns (address[] memory values);
    function envBytes32(string calldata key) external returns (bytes32 value);
    function envBytes32(string calldata key, string calldata delimiter) external returns (bytes32[] memory values);
    function envString(string calldata key) external returns (string memory value);
    function envString(string calldata key, string calldata delimiter) external returns (string[] memory values);
    function envBytes(bytes calldata key) external returns (bytes memory value);
    function envBytes(bytes calldata key, bytes calldata delimiter) external returns (bytes[] memory values);
    function toString(address value) external returns (string memory);
    function toString(bool value) external returns (string memory);
    function toString(uint256 value) external returns (string memory);
    function toString(int256 value) external returns (string memory);
    function toString(bytes32 value) external returns (string memory);
    function toString(bytes memory value) external returns (string memory);
}

contract HasStorage {
    uint slot0 = 10;
}

contract Prankster {
    function prankme() public returns (address) {
        return msg.sender;
    }
}

contract Payable {
    function hi() public payable {}
    receive() external payable {}
}

contract Empty {}

contract CheatCodes is Test {
    address store = address(new HasStorage());
    address constant HEVM_ADDRESS =
        address(bytes20(uint160(uint256(keccak256('hevm cheat code')))));
    Hevm hevm = Hevm(HEVM_ADDRESS);

    function prove_warp_concrete() public {
        uint jump = 1000;
        uint pre = block.timestamp;
        hevm.warp(block.timestamp + jump);
        assertEq(block.timestamp, pre + jump);
    }

    function prove_warp_symbolic(uint128 jump) public {
        uint pre = block.timestamp;
        hevm.warp(block.timestamp + jump);
        assertEq(block.timestamp, pre + jump);
    }

    function prove_roll_concrete() public {
        uint jump = 1000;
        uint pre = block.number;
        hevm.roll(block.number + jump);
        assertEq(block.number, pre + jump);
    }

    function prove_store_load_concrete() public {
        uint x = 1000;
        uint ten = uint(hevm.load(store, bytes32(0)));
        assertEq(ten, 10);

        hevm.store(store, bytes32(0), bytes32(x));
        uint val = uint(hevm.load(store, bytes32(0)));
        assertEq(val, x);
    }

    function prove_store_load_symbolic(uint x) public {
        uint ten = uint(hevm.load(store, bytes32(0)));
        assertEq(ten, 10);

        hevm.store(store, bytes32(0), bytes32(x));
        uint val = uint(hevm.load(store, bytes32(0)));
        assertEq(val, x);
    }

    function prove_sign_addr_digest() public {
        uint sk = 1000000;
        bytes32 digest = "123456789";

        (uint8 v, bytes32 r, bytes32 s) = hevm.sign(sk, digest);
        address expected = hevm.addr(sk);
        address actual = ecrecover(digest, v, r, s);

        assertEq(actual, expected);
    }

    function proveFail_sign_addr() public {
        uint sk = 999;
        bytes32 digest = "abcdef123456";
        uint badKey = sk + 1;

        (uint8 v, bytes32 r, bytes32 s) = hevm.sign(badKey, digest);
        address expected = hevm.addr(sk);
        address actual = ecrecover(digest, v, r, s);

        assertEq(actual, expected);
    }

    function proveFail_addr_zero_sk() public {
        hevm.addr(0);
    }

    function proveFFI() public {
        string[] memory inputs = new string[](3);
        inputs[0] = "echo";
        inputs[1] = "-n";
        inputs[2] = "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000046163616200000000000000000000000000000000000000000000000000000000";

        (string memory output) = abi.decode(hevm.ffi(inputs), (string));
        assertEq(output, "acab");
    }

    function prove_env_FFI() public {
        hevm.setEnv("HEVM_TXT_TEST", "0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000046163616200000000000000000000000000000000000000000000000000000000");
        string[] memory inputs = new string[](3);
        inputs[0] = "sh";
        inputs[1] = "-c";
        inputs[2] = "echo -n $HEVM_TXT_TEST";

        (string memory output) = abi.decode(hevm.ffi(inputs), (string));
        assertEq(output, "acab");
    }

    function prove_envBool() public {
        string memory varname = "ENV_BOOL_TEST";

        hevm.setEnv(varname, "true");
        assert(hevm.envBool(varname));
        hevm.setEnv(varname, "True");
        assert(hevm.envBool(varname));

        hevm.setEnv(varname, "false");
        assert(!hevm.envBool(varname));
        hevm.setEnv(varname, "False");
        assert(!hevm.envBool(varname));

        hevm.setEnv(varname, "true,True,False,false");
        bool[] memory result = hevm.envBool(varname, ",");
        assertEq(result.length, 4);
        assert(result[0] && result[1] && !result[2] && !result[3]);

        hevm.setEnv(varname, "invalid");
        try hevm.envBool(varname) returns (bool) {
            assert(false);
        } catch Error(string memory reason) {
            assertEq(reason, "invalid value");
        } catch (bytes memory reason) {
            assert(false);
        }

        try hevm.envBool(varname, ",") returns (bool[] memory) {
            assert(false);
        } catch Error(string memory reason) {
            assertEq(reason, "invalid value");
        } catch (bytes memory reason) {
            assert(false);
        }
    }

    function prove_envUint() public {
        string memory varname = "ENV_UINT_TEST";

        hevm.setEnv(varname, "0");
        assertEq(hevm.envUint(varname), 0);
        hevm.setEnv(varname, "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        assertEq(hevm.envUint(varname), type(uint256).max);
        hevm.setEnv(varname, "1234");
        assertEq(hevm.envUint(varname), 1234);


        hevm.setEnv(varname, "0,115792089237316195423570985008687907853269984665640564039457584007913129639935,0x0000000000000000000000000000000000000000000000000000000000000000");
        uint[] memory result = hevm.envUint(varname, ",");
        assertEq(result.length, 3);
        assertEq(result[0], 0);
        assertEq(result[1], type(uint256).max);
        assertEq(result[2], 0);

        hevm.setEnv(varname, "invalid");
        try hevm.envUint(varname) returns (uint) {
            assert(false);
        } catch Error(string memory reason) {
            assertEq(reason, "invalid W256 value");
        } catch (bytes memory reason) {
            assert(false);
        }
    }

    function prove_envInt() public {
        string memory varname = "ENV_INT_TEST";

        hevm.setEnv(varname, "0");
        assertEq(hevm.envInt(varname), 0);
        hevm.setEnv(varname, "0x8000000000000000000000000000000000000000000000000000000000000000");
        assertEq(hevm.envInt(varname), type(int256).min);
        hevm.setEnv(varname, "-1234");
        assertEq(hevm.envInt(varname), -1234);


        hevm.setEnv(varname, "0,115792089237316195423570985008687907853269984665640564039457584007913129639935,0x0000000000000000000000000000000000000000000000000000000000000000");
        int[] memory result = hevm.envInt(varname, ",");
        assertEq(result.length, 3);
        assertEq(result[0], 0);
        assertEq(result[1], -1);
        assertEq(result[2], 0);

        hevm.setEnv(varname, "invalid");
        try hevm.envInt(varname) returns (int) {
            assert(false);
        } catch Error(string memory reason) {
            assertEq(reason, "invalid Int256 value");
        } catch (bytes memory reason) {
            assert(false);
        }
    }

    function prove_envAddress() public {
        string memory varname = "ENV_ADDR_TEST";

        hevm.setEnv(varname, "0");
        assertEq(hevm.envAddress(varname), address(0));
        hevm.setEnv(varname, "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D");
        assertEq(hevm.envAddress(varname), 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
        hevm.setEnv(varname, "0x1000");
        assertEq(hevm.envAddress(varname), address(0x1000));


        hevm.setEnv(varname, "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D,0x0000000000000000000000000000000000000000");
        address[] memory result = hevm.envAddress(varname, ",");
        assertEq(result.length, 2);
        assertEq(result[0], 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
        assertEq(result[1], 0x0000000000000000000000000000000000000000);

        hevm.setEnv(varname, "0xinvalid");
        try hevm.envAddress(varname) returns (address) {
            assert(false);
        } catch Error(string memory reason) {
            assertEq(reason, "invalid address value");
        } catch (bytes memory reason) {
            assert(false);
        }
    }

    function prove_envBytes32() public {
        string memory varname = "ENV_BYTES32_TEST";

        hevm.setEnv(varname, "0");
        assertEq(hevm.envBytes32(varname), 0);
        hevm.setEnv(varname, "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
        assertEq(hevm.envBytes32(varname), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
        hevm.setEnv(varname, "1234");
        assertEq(hevm.envBytes32(varname), bytes32(uint(1234)));


        hevm.setEnv(varname, "0,0x7109709ECfa91a80626fF3989D68f67F5b1DD12D,0x0000000000000000000000000000000000000000000000000000000000000000");
        bytes32[] memory result = hevm.envBytes32(varname, ",");
        assertEq(result.length, 3);
        assertEq(result[0], 0);
        assertEq(result[1], 0x0000000000000000000000007109709ECfa91a80626fF3989D68f67F5b1DD12D);
        assertEq(result[2], 0);

        hevm.setEnv(varname, "invalid");
        try hevm.envBytes32(varname) returns (bytes32) {
            assert(false);
        } catch Error(string memory reason) {
            assertEq(reason, "invalid bytes32 value");
        } catch (bytes memory reason) {
            assert(false);
        }
    }

    function prove_envString() public {
        string memory varname = "ENV_STRING_TEST";

        hevm.setEnv(varname, "hello, world!");
        assertEq(hevm.envString(varname), "hello, world!");

        hevm.setEnv(varname, "hevm|eth||0xffff");
        string[] memory result = hevm.envString(varname, "|");
        assertEq(result.length, 4);
        assertEq(result[0], "hevm");
        assertEq(result[1], "eth");
        assertEq(result[2], "");
        assertEq(result[3], "0xffff");
    }

    function prove_invalidUTF8() public {
        // ABI strings are raw bytes and need not be valid UTF-8: byte 0xbf
        // must not crash cheatcode string handling (issue #1076)
        string memory invalid = string(abi.encodePacked(hex"bf"));

        hevm.setEnv(invalid, "hello, world!");
        assertEq(hevm.envString(invalid), "hello, world!");

        hevm.label(address(this), invalid);
    }

    function prove_envBytes() public {
        bytes memory varname = "ENV_BYTES_TEST";

        hevm.setEnv(string(varname), "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D");
        assert(keccak256(abi.encodePacked(hevm.envBytes(varname))) == keccak256(abi.encodePacked(hex"7109709ECfa91a80626fF3989D68f67F5b1DD12D")));

        hevm.setEnv(string(varname), "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D,0x00");
        bytes[] memory result = hevm.envBytes(varname, ",");
        assertEq(result.length, 2);
        assert(keccak256(abi.encodePacked(result[0])) == keccak256(abi.encodePacked(hex"7109709ECfa91a80626fF3989D68f67F5b1DD12D")));
        assert(keccak256(abi.encodePacked(result[1])) == keccak256(abi.encodePacked(hex"00")));

        hevm.setEnv(string(varname), "invalid");
        try hevm.envBytes(varname) returns (bytes memory) {
            assert(false);
        } catch Error(string memory reason) {
            assertEq(reason, "invalid bytes value");
        } catch (bytes memory reason) {
            assert(false);
        }
    }

    function prove_prank() public {
        Prankster prankster = new Prankster();
        assertEq(prankster.prankme(), address(this));
        hevm.prank(address(0xdeadbeef));
        assertEq(prankster.prankme(), address(0xdeadbeef));
        assertEq(prankster.prankme(), address(this));
    }

    function prove_prank(address caller) public {
        Prankster prankster = new Prankster();
        assertEq(prankster.prankme(), address(this));
        hevm.prank(caller);
        assertEq(prankster.prankme(), caller);
        assertEq(prankster.prankme(), address(this));
    }


    function prove_startPrank(address caller) public {
        Prankster prankster = new Prankster();
        assertEq(prankster.prankme(), address(this));

        hevm.startPrank(address(0xdeadbeef));
        assertEq(prankster.prankme(), address(0xdeadbeef));
        assertEq(prankster.prankme(), address(0xdeadbeef));
        hevm.stopPrank();

        hevm.startPrank(caller);
        assertEq(prankster.prankme(), caller);
        assertEq(prankster.prankme(), caller);
        hevm.stopPrank();

        assertEq(prankster.prankme(), address(this));

        hevm.prank(caller);
        assertEq(prankster.prankme(), caller);
        assertEq(prankster.prankme(), address(this));
    }

    // this is not supported yet due to restrictions around symbolic address aliasing...
    function proveFail_deal_unknown_address(address e, uint val) public {
        hevm.deal(e, val);
        assert(e.balance == val);
    }

    function prove_deal_simple(uint val) public {
        address e = address(new Empty());
        assert(e.balance == 0);
        hevm.deal(e, val);
        assert(e.balance == val);
    }

    function prove_deal_no_underflow(uint val) public {
        require(address(this).balance < val);
        prove_deal_simple(val);
    }

    function prove_deal_multiple(uint val1, uint val2) public {
        address e = address(new Empty());

        assert(e.balance == 0);
        hevm.deal(e, val1);
        assert(e.balance == val1);

        hevm.deal(e, val2);
        assert(e.balance == val2);
    }

    function prove_assume(bool b) public {
        hevm.assume(b);
        assert(b);
    }

    function prove_assume(uint v) public {
        hevm.assume(v > 10);
        assert(v > 10);
    }

    function proveFail_assume(uint v) public {
        hevm.assume(v > 10);
        assert(v <= 10);
    }

    function proveFail_assume(bool b) public {
        hevm.assume(b);
        assert(!b);
    }

    function prove_prank_val() public {
        address from = address(0x1312);
        uint amt = 10;

        Payable target = new Payable();
        from.call{value: amt}("");

        uint preBal = from.balance;

        hevm.prank(from);
        target.hi{value : amt}();

        uint postBal = from.balance;

        assertEq(preBal - postBal, amt);
    }

    function prove_prank_val_2() public {
        address payable a = payable(address(new Payable()));
        address payable b = payable(address(new Payable()));

        // send this.balance to a
        a.call{value: address(this).balance}("");
        uint aBal = a.balance;

        // send 1 wei from a to b
        hevm.prank(a);
        address(b).call{value: 1}("");

        // check balances
        assertEq(a.balance, aBal - 1);
        assertEq(b.balance, 1);
    }

    function prove_startPrank_val() public {
        address payable a = payable(address(new Payable()));
        address payable b = payable(address(new Payable()));

        // send this.balance to a
        a.call{value: address(this).balance}("");
        uint aBal = a.balance;

        // send 1 wei from a to b
        hevm.startPrank(a);
        address(b).call{value: 1}("");
        address(b).call{value: 1}("");
        hevm.stopPrank();

        // check balances
        assertEq(a.balance, aBal - 2);
        assertEq(b.balance, 2);
    }

    function prove_label_works() public {
        hevm.label(address(this), "label");
        assert(true);
    }

    function prove_toString_address() public {
        address testAddr = address(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
        string memory result = hevm.toString(testAddr);
        assertEq(result, "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D");

        address zeroAddr = address(0);
        string memory zeroResult = hevm.toString(zeroAddr);
        assertEq(zeroResult, "0x0000000000000000000000000000000000000000");
    }

    function prove_toString_bool() public {
        string memory trueResult = hevm.toString(true);
        assertEq(trueResult, "true");

        string memory falseResult = hevm.toString(false);
        assertEq(falseResult, "false");
    }

    function prove_toString_uint256() public {
        string memory zeroResult = hevm.toString(uint256(0));
        assertEq(zeroResult, "0");

        string memory smallResult = hevm.toString(uint256(123));
        assertEq(smallResult, "123");

        string memory maxResult = hevm.toString(type(uint256).max);
        assertEq(maxResult, "115792089237316195423570985008687907853269984665640564039457584007913129639935");
    }

    function prove_toString_int256() public {
        string memory zeroResult = hevm.toString(int256(0));
        assertEq(zeroResult, "0");

        string memory positiveResult = hevm.toString(int256(123));
        assertEq(positiveResult, "123");

        string memory negativeResult = hevm.toString(int256(-123));
        assertEq(negativeResult, "-123");

        string memory minResult = hevm.toString(type(int256).min);
        assertEq(minResult, "-57896044618658097711785492504343953926634992332820282019728792003956564819968");

        string memory maxResult = hevm.toString(type(int256).max);
        assertEq(maxResult, "57896044618658097711785492504343953926634992332820282019728792003956564819967");
    }

    function prove_toString_bytes32() public {
        bytes32 testBytes = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D000000000000000000000000;
        string memory result = hevm.toString(testBytes);
        assertEq(result, "0x7109709ecfa91a80626ff3989d68f67f5b1dd12d000000000000000000000000");

        bytes32 zeroBytes = bytes32(0);
        string memory zeroResult = hevm.toString(zeroBytes);
        assertEq(zeroResult, "0x0000000000000000000000000000000000000000000000000000000000000000");
    }

    function prove_toString_bytes() public {
        bytes memory testBytes = hex"7109709ECfa91a80626fF3989D68f67F5b1DD12D";
        string memory result = hevm.toString(testBytes);
        assertEq(result, "0x7109709ecfa91a80626ff3989d68f67f5b1dd12d");

        bytes memory emptyBytes = "";
        string memory emptyResult = hevm.toString(emptyBytes);
        assertEq(emptyResult, "0x");

        bytes memory shortBytes = hex"acab";
        string memory shortResult = hevm.toString(shortBytes);
        assertEq(shortResult, "0xacab");
    }
}
