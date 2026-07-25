{- |
    Module: EVM.HashCons
    Description: Public entry points for construction-time hash-consing of Expr.

    The machinery itself no longer lives here. Interning happens inside the Expr pattern synonyms
    (EVM.Types), so every construction site in the interpreter shares structurally equal subterms
    as they are produced: a computation that reuses an intermediate at k nesting levels stays a
    DAG instead of materializing a 2^k tree. The memoized simplification pass lives next to the
    traversal it reuses (EVM.Traversals.memoFixTraverse).

    This module used to be 556 lines: a StableName side table with a type-erased existential to
    map nodes back to ids, a hand-maintained structural key (72 constructor tag numbers plus a
    Payload sum type enumerating every scalar field), and a 200-line copy of mapExprM. All of it
    is gone. Nodes carry their own id, the structural key is derived from the datatype, and there
    is one traversal.

    Note on 'setHashConsEnabled': it must be set before any Expr is constructed, and not toggled
    afterwards. Nodes built while it was off carry @ident == 0@, and the smart constructor then
    refuses to key anything above them, so flipping it on mid-run silently buys nothing.
-}
module EVM.HashCons
  ( setHashConsEnabled
  , resetHashCons
  , hashConsEnabled
  , memoFixTraverse
  ) where

import EVM.Traversals (memoFixTraverse)
import EVM.Types (setHashConsEnabled, resetHashCons, hashConsEnabled)
