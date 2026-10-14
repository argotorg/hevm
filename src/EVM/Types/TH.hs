{-# LANGUAGE TemplateHaskell #-}

{- |
    Module: EVM.Types.TH
    Description: Eq and Ord bodies for Expr that check physical identity before every comparison

    The derived instances recurse into themselves, so there is nowhere to put the check; these
    generate the comparisons the compiler would derive, with it added. The generated code refers
    to @ptrEq@ and @exprRank@, which must be in scope at the splice.
-}
module EVM.Types.TH (shortcutEq, shortcutCompare, constructors) where

import Control.Monad (replicateM)
import Language.Haskell.TH

-- | @\\l r -> ...@ for '(==)'
shortcutEq :: Name -> Q Exp
shortcutEq = shortcut Cmp
  { same = [| True |]
  , other = \_ _ -> [| False |]
  , field = \a b -> [| $ptrEq $a $b || $a == $b |]
  , combine = \x y -> [| $x && $y |]
  }

-- | @\\l r -> ...@ for 'compare', ordering constructors by declaration and then fields left to
-- right, as the derived instance does
shortcutCompare :: Name -> Q Exp
shortcutCompare = shortcut Cmp
  { same = [| EQ |]
  , other = \l r -> [| compare ($rank $l) ($rank $r) |]
  , field = \a b -> [| if $ptrEq $a $b then EQ else compare $a $b |]
  , combine = \x y -> [| $x <> $y |]
  }
  where rank = varE (mkName "exprRank")

ptrEq :: Q Exp
ptrEq = varE (mkName "ptrEq")

data Cmp = Cmp
  { same    :: Q Exp                        -- ^ both sides are one object, or equal nullary constructors
  , other   :: Q Exp -> Q Exp -> Q Exp      -- ^ different constructors
  , field   :: Q Exp -> Q Exp -> Q Exp      -- ^ one pair of fields
  , combine :: Q Exp -> Q Exp -> Q Exp      -- ^ the results of two field comparisons
  }

shortcut :: Cmp -> Name -> Q Exp
shortcut cmp ty = do
  cons <- constructors ty
  l <- newName "l"
  r <- newName "r"
  let alt (c, fs) = do
        let n = length fs
        as <- replicateM n (newName "a")
        bs <- replicateM n (newName "b")
        let fields = zipWith cmp.field (fmap varE as) (fmap varE bs)
            body = if null fields then cmp.same else foldr1 cmp.combine fields
        match (conP c (fmap varP as))
          (normalB (caseE (varE r)
            [ match (conP c (fmap varP bs)) (normalB body) []
            , match wildP (normalB (cmp.other (varE l) (varE r))) [] ]))
          []
  lamE [varP l, varP r]
    [| if $ptrEq $(varE l) $(varE r) then $(cmp.same) else $(caseE (varE l) (fmap alt cons)) |]

-- | The constructors of a data type, with their field types
constructors :: Name -> Q [(Name, [Type])]
constructors ty = reify ty >>= \case
  TyConI (DataD _ _ _ _ cons _) -> pure (concatMap con cons)
  _ -> fail ("not a data type: " <> show ty)
  where
    con = \case
      NormalC n fs -> [(n, fmap snd fs)]
      RecC n fs -> [(n, [t | (_, _, t) <- fs])]
      InfixC (_, a) n (_, b) -> [(n, [a, b])]
      GadtC ns fs _ -> [(n, fmap snd fs) | n <- ns]
      RecGadtC ns fs _ -> [(n, [t | (_, _, t) <- fs]) | n <- ns]
      ForallC _ _ c -> con c
