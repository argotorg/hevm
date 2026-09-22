contract C {
  bool public IS_TEST = true;
  function prove_abort(uint a, uint b, uint x) public {
    if (x == 7) {
      assert(false);
    } else {
      uint c;
      unchecked { c = (a * b) % 982374892374389278894734; }
      assert(c != 278198683154907855159120);
    }
  }
}
