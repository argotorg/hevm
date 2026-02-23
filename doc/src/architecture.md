# Steppers & Interpreters
The core EVM semantics in hevm can be found in `EVM.hs`. EVM state is contained
in the `VM` record, and the `exec1` function executes a single opcode inside
the monad `type EVM a = State VM a`.

The core semantics are pure, and should information from the outside world be
required to continue execution (RPC queries or SMT queries),
execution will halt, and the `result` field of the VM will be an instance of
`VMFailure (Query _)`.

Multiple steps of EVM execution are orchestrated via interpreters for a meta
language. Programs in the meta language are called Steppers. The instructions
in the meta language can be found in `Stepper.hs`.

There can potentially be many different interpreters with different features. Currently,
we provide a concrete and a symbolic interpreter. Interpreters can
handle Queries in different ways, for example in the symbolic interpreter, both
sides of a branch point will be explored, while in the concrete interpreter,
such branching is not permitted.

Interpreters are parametrized by a `Fetcher` that can handle RPC and SMT
queries, and can be instantiated with fetchers that could have different
fetching strategies (e.g. caching). Interpreters execute Steppers and use their
Fetcher to handle any Queries that need to be resolved.

This architecture is very modular and pluggable, and allows the core semantics
to be shared between different interpreters, as well as the reuse of steppers
between different interpreters, making it easy to e.g. share the same test
execution strategy between concrete and symbolic interpreters.
```mermaid
graph LR
    subgraph meta-language
    A[Stepper]
    end
    subgraph interpreters
    A --> B[Concrete]
    A --> C[Symbolic]
    end
    subgraph fetchers
    F[Fetch.hs]
    B --> F
    C --> F
    end
    subgraph EVM Semantics
    G[EVM.hs]
    B --> G
    C --> G
    end
```

# Expr
The symbolic execution features in hevm are built using a custom IR,
imaginatively named `Expr`. This is a summarized trace semantics of a given
EVM program.

One important principle is that of local context: e.g. each term representing a
read from a Buf/Storage will always contain a snapshot of the state of the
buffer/store at the time the read occurred. This ensures that all context
relevant to a given operation is contained within the term that represents that
operation, and allows subsequent analysis to be stateless.

Expressions in this language can have the following types:
- `End`: control flow
- `Word`: a 256 bit word (a stack item)
- `Byte`: a single byte
- `Buf`: a byte array (used for calldata, memory and returndata)
- `Storage`: contract storage
- `Logs`: EVM logs

## Control Flow
An EVM program is represented by an `[Expr End]`, which is a list of all
possible end states for a program. As an example the following
two `Expr End`-s encode a program that branches based on the equality of two symbolic
words ("a" and "b"), and returns if they are equal and reverts if they are not:
```haskell
[ Success [PEq (Var "a") (Var "b")] ...,
, Failure [PNeg (PEq (Var "a") (Var "b"))] ...]
```

## Buffers
Memory, calldata, and returndata are all represented as a Buf. Semantically
speaking a Buf is a byte array with of size 2^256.

Bufs have three base constructors:
  - AbstractBuf:    all elements are fully abstract values
  - ConcreteBuf bs: all elements past (length bs) are zero

Bufs can be read from with:
  - ReadByte idx buf: read the byte at idx from buf
  - ReadWord idx buf: read the byte at idx from buf

Bufs can be written to with:
  - WriteByte idx val buf: write val to idx in buf
  - WriteWord idx val buf: write val to idx in buf
  - CopySlice srcOffset dstOffset size src dst:
      overwrite dstOffset -> dstOffset + size in dst with srcOffset -> srcOffset + size from src

e.g. the following Buf expression represents an abi encoded call to `foo(uint256 a)`:
```haskell
(WriteWord (Lit 0x4) (Var "a")
(WriteByte (Lit 0x3) (LitByte 56)
(WriteByte (Lit 0x2) (LitByte 189)
(WriteByte (Lit 0x1) (LitByte 190)
(WriteByte (Lit 0x0) (LitByte 47)
(AbstractBuf "txdata")))))
```

This represents calldata of the form:
```
-----------------------------------------------------------------------
| <function selector> | <symbolic word> | arbitrary symbolic data.... |
-----------------------------------------------------------------------
```

Note that a Buf expression contains a copy of all historical writes, meaning
that it is possible to write multiple times to the same location. In this case
only the topmost write is relevant. This allows us to mix symbolic and concrete
writes to the same buffer.

## Storage
Storage expressions are similar, but instead of writing regions of bytes, we
write a word to a particular key in a given addresses storage. Note that as
with a Buf, writes can be sequenced on top of concrete, empty and fully
abstract starting states.

As with Bufs, Storage expressions contain a full history of all previous writes.

For example the following expression represents a write of a symbolic word "c"
to slot 2 for the zero address followed by a write of 1 to the slot at the
symbolic location "b" for the zero address. These writes are sequenced on top
of an `EmptyStore` meaning all other storage locations are held to be 0.
```haskell
(SStore (Lit 0) (Var "b") (Lit 1)
(SStore (Lit 0) (Lit 2) (Var "c")
EmptyStore))
```

## Logs
Logs are also represented as a sequence of writes, but unlike Buf and Storage
expressions, Log writes are always sequenced on an empty starting point, and
overwriting is not allowed.

# Symbolic Execution
During symbolic execution all possible branches of the program are explored
symbolically. Reachability analysis is performed at this stage only if needed
for loop unrolling. This produces an Expr End. As an example consider the
following program:
```solidity
contract MyContract {
  mapping(uint => uint) items;
  function test(uint val1) public {
    require(val1 > 10);
    unchecked {
      items[4] = val1+1;
      assert(items[4] > 10);
    }
  }
}
```

This decompiles into the following Expr End:
![Body frame](expr.png)

For more details, see our research paper on hevm on open access
[research
paper](https://link.springer.com/content/pdf/10.1007/978-3-031-65627-9_22.pdf?pdf=inline+link)
as presented at CAV 2024, [presentation
here](https://github.com/msooseth/hevm-presentation/blob/main/HEVM-presentation%20CAV%2026th%20July%202024.pdf)
