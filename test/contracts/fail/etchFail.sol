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
  function prove_etch_fail(int i) external {
    // to make sure not all branches revert
    if (i < 0) {
      return;
    }
    bytes memory bCode = address(b).code;
    Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    assert(a.getX() == 10);
    vm.etch(address(a), bCode);
    assert(a.getX() == 10);
  }
}
