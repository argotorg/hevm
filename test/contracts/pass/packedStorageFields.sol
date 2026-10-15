// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract PackedStorageFields {
    bool public constant IS_TEST = true;

    struct Fields {
        uint32 prefix;
        uint32 lower;
        uint32 upper;
        uint160 suffix;
    }

    Fields private fields;

    function prove_read_back(uint32 prefix, uint32 lower, uint32 upper, uint160 suffix) public {
        fields.prefix = prefix;
        fields.suffix = suffix;
        fields.lower = lower;
        fields.upper = upper;

        assert(fields.lower == lower);
        assert(fields.upper == upper);
        assert(fields.prefix == prefix);
        assert(fields.suffix == suffix);
    }
}
