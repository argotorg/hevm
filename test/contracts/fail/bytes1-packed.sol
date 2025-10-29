contract C {
  bool public IS_TEST = true;
  uint256 state;

  function prop() public view {
    assert(state == 0);
  }

  function inc() external { state++; }

  function prove_callAndCheckProperty(bytes1[36] calldata arr) external {
    address target = address(this);
    bool success;
    assembly {
      // Allocate memory for the calldata copy
      let dataPtr := mload(0x40)
      let dataLen := 36 // N = 32 bytes

      // Copy calldata (after 4-byte selector) into memory
      calldatacopy(dataPtr, 0x04, dataLen)

      // Update the free memory pointer
      mstore(0x40, add(dataPtr, dataLen))

      // Perform the low-level call
      // this should call the inc() function, which has selector:
      //```
      //cast keccak "inc()"
      //0x371303c051bff726100ad13871cababf50c20dd920fca137e519f98f089a74b4
      //```
      // which happens to have the first 4 bytes as
      // 0x37, 0x13 0x03, 0xc0
      // This will increment `state` by 1, thereby violating the property

      success := call(gas(), target, 0, dataPtr, dataLen, 0, 0)
    }

    if (!success) revert("raw call failed");
    prop();
  }
}
