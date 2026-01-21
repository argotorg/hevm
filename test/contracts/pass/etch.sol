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
  }
}
