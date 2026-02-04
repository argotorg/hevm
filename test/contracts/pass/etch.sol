import "forge-std/Test.sol";

contract A {
  function getX() external returns (uint) {
      return 10;
  }
}
contract B {
  function getX() external returns (uint) {
      return 20;
  }
  function getY() external returns (uint) {
      return 30;
  }
}
contract C is Test{
  A a;
  B b;
  function setUp() public {
      a = new A();
      b = new B();
  }
  function prove_etch() external {
      bytes memory bCode = address(b).code;
      Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

      assert(a.getX() == 10);
      vm.etch(address(a), bCode);
      assert(address(a).code.length == address(b).code.length);
      bytes memory aCode = address(a).code;
      assert(keccak256(aCode) == keccak256(bCode));
      assert(a.getX() == 20);
      assert(B(address(a)).getY() == 30);
  }

  function prove_etch_fresh_address() external {
      address fresh = address(0xDEADBEEF);
      bytes memory bCode = address(b).code;
      Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

      // zero codehash (non-existent account)
      assert(fresh.codehash == bytes32(0));

      vm.etch(fresh, bCode);

      assert(fresh.code.length == bCode.length);
      assert(B(fresh).getX() == 20);
      assert(keccak256(fresh.code) == keccak256(bCode));
  }

  function prove_deal_then_etch() external {
      address fresh = address(0xBEEFCAFE);
      bytes memory bCode = address(b).code;
      Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

      vm.deal(fresh, 100 ether);

      // codehash of empty code
      bytes32 emptyCodehash = keccak256("");
      assert(fresh.codehash == emptyCodehash);

      vm.etch(fresh, bCode);
      assert(B(fresh).getX() == 20);
      assert(fresh.balance == 100 ether);
  }

  function prove_etch_then_deal() external {
      address fresh = address(0xDEADCAFE);
      bytes memory bCode = address(b).code;
      Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

      vm.etch(fresh, bCode);
      assert(B(fresh).getX() == 20);

      vm.deal(fresh, 50 ether);

      assert(B(fresh).getX() == 20);
      assert(fresh.balance == 50 ether);
  }
}
