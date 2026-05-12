// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.26;

import {Test} from "forge-std/Test.sol";

// =============================================================================
// Group A: single-contract bytes[] baseline.
//   - BytesArrayStore exposes `bytes[] public arr`, populated concretely in
//     setUp via Solidity-level push.
//   - prove_arr_read(i) reads arr(i) with symbolic i, exercising the
//     auto-generated getter's SLOAD->MSTORE long-bytes loop.
// =============================================================================

contract BytesArrayStore {
    bytes[] public arr;

    function init() external {
        // Each element is >32 bytes to force the long-bytes branch and the
        // copy loop inside the auto-generated arr(uint256) getter.
        arr.push("0123456789abcdefghijklmnopqrstuvwxyz");        // 36 bytes
        arr.push("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!!");       // 38 bytes
    }
}

contract TestBytesArrayBaseline is Test {
    BytesArrayStore store;

    function setUp() public {
        store = new BytesArrayStore();
        store.init();
    }

    function prove_arr_read(uint256 i) public view {
        require(i < 2);
        bytes memory b = store.arr(i);
        // Touch the result so the call isn't dead-code-eliminated.
        require(b.length >= 0);
    }
}

// =============================================================================
// Group B: cross-contract reader.
//   - Producer holds the bytes[] storage.
//   - Consumer is a separate contract that reads producer.chunks(i) and
//     re-exposes it. The test calls Consumer.readChunk(i) with symbolic i.
// =============================================================================

contract ChunkProducer {
    bytes[] public chunks;

    function init() external {
        chunks.push("the quick brown fox jumps over the lazy dog");   // 43 bytes
        chunks.push("pack my box with five dozen liquor jugs!!!!!");  // 44 bytes
    }
}

contract ChunkConsumer {
    ChunkProducer producer;

    constructor(ChunkProducer _p) {
        producer = _p;
    }

    function readChunkLength(uint256 i) external view returns (uint256) {
        bytes memory b = producer.chunks(i);
        return b.length;
    }
}

contract TestCrossContractBytesArray is Test {
    ChunkProducer producer;
    ChunkConsumer consumer;

    function setUp() public {
        producer = new ChunkProducer();
        producer.init();
        consumer = new ChunkConsumer(producer);
    }

    function prove_consumer_reads(uint256 i) public view {
        require(i < 2);
        uint256 len = consumer.readChunkLength(i);
        require(len >= 0);
    }
}

// =============================================================================
// Group C1: NFT-style metadata registry.
//   Realistic shape: registry stores token URIs as bytes; a separate
//   verifier contract reads and checks length is within a bound.
// =============================================================================

contract NFTRegistry {
    bytes[] public tokenURIs;

    function init() external {
        // Long URIs to force the SLOAD->MSTORE loop.
        tokenURIs.push("ipfs://QmExampleHashForTokenOne00000000000");   // 40 bytes
        tokenURIs.push("ipfs://QmExampleHashForTokenTwo00000000000");   // 40 bytes
        tokenURIs.push("ipfs://QmExampleHashForTokenThree000000000");   // 40 bytes
    }
}

contract URIVerifier {
    NFTRegistry registry;

    constructor(NFTRegistry _r) {
        registry = _r;
    }

    /// @notice Returns true if tokenURI fits in `maxLen` bytes.
    function checkURILength(uint256 tokenId, uint256 maxLen) external view returns (bool) {
        bytes memory uri = registry.tokenURIs(tokenId);
        return uri.length <= maxLen;
    }
}

contract TestNFTRegistry is Test {
    NFTRegistry registry;
    URIVerifier verifier;

    function setUp() public {
        registry = new NFTRegistry();
        registry.init();
        verifier = new URIVerifier(registry);
    }

    function prove_uri_length(uint256 tokenId, uint256 maxLen) public view {
        require(tokenId < 3);
        // Just exercises the read path through the verifier; we don't
        // assert anything about the boolean return.
        bool ok = verifier.checkURILength(tokenId, maxLen);
        require(ok || !ok);
    }
}

// =============================================================================
// Group C2: Merkle-proof-style reader.
//   Storage contract holds bytes[] of proofs; verifier reads one and checks
//   shape (length multiple of 32) — a real precondition for Merkle proofs.
// =============================================================================

contract ProofStore {
    bytes[] public proofs;

    function init() external {
        // 64- and 96-byte proofs (2 and 3 hashes respectively).
        proofs.push(hex"0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40");
        proofs.push(hex"0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f60");
    }
}

contract MerkleVerifier {
    ProofStore store;

    constructor(ProofStore _s) {
        store = _s;
    }

    /// @notice Reads proof i and checks its byte-length is a multiple of 32.
    function isWellFormed(uint256 i) external view returns (bool) {
        bytes memory p = store.proofs(i);
        return p.length % 32 == 0;
    }
}

contract TestMerkleProofs is Test {
    ProofStore store;
    MerkleVerifier verifier;

    function setUp() public {
        store = new ProofStore();
        store.init();
        verifier = new MerkleVerifier(store);
    }

    function prove_proof_shape(uint256 i) public view {
        require(i < 2);
        bool ok = verifier.isWellFormed(i);
        require(ok || !ok);
    }
}
