contract C {
  bool public IS_TEST = true;
  function prove_stuff(uint a) public {
    for(uint i = 0; i < 10; i++) {
    unchecked {
      assert(i * a < 100);
      }
    }
  }
}
