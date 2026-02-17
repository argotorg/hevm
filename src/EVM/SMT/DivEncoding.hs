{- | Abstract div/mod encoding for two-phase SMT solving. -}
module EVM.SMT.DivEncoding
  ( divModGroundAxioms
  , assertProps
  , assertPropsAbstract
  , assertPropsShiftBounds
  ) where

import Data.Bits ((.&.), countTrailingZeros)
import Data.Containers.ListUtils (nubOrd)
import Data.List (groupBy, sortBy, nubBy)
import Data.Ord (comparing)
import Data.Text.Lazy.Builder

import EVM.Effects
import EVM.SMT
import EVM.Traversals
import EVM.Types (Prop(..), EType(EWord), Err, W256, Expr, Expr(Lit), Expr(SHL))
import EVM.Types qualified as T

assertPropsAbstract :: Config -> [Prop] -> Err SMT2
assertPropsAbstract conf ps = do
  let mkBase simp = assertPropsHelperWith AbstractDivision simp divModAbstractDecls
  base <- if not conf.simp then mkBase False ps
          else mkBase True (decompose conf ps)
  bounds <- divModBounds ps
  pure $ base <> SMT2 (SMTScript bounds) mempty mempty


assertProps :: Config -> [Prop] -> Err SMT2
assertProps conf ps =
  if not conf.simp then assertPropsHelperWith ConcreteDivision False [] ps
  else assertPropsHelperWith ConcreteDivision True [] (decompose conf ps)

-- | Uninterpreted function declarations for abstract div/mod.
divModAbstractDecls :: [SMTEntry]
divModAbstractDecls =
  [ SMTComment "abstract division/modulo (uninterpreted functions)"
  , SMTCommand "(declare-fun abst_evm_bvudiv ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_bvsdiv ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_bvurem ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  , SMTCommand "(declare-fun abst_evm_bvsrem ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))"
  ]

exprToSMTAbst :: Expr a -> Err Builder
exprToSMTAbst = exprToSMTWith AbstractDivision

-- | Result of div(a,b) is always <= a, and result of mod(a,b) is always <= b
-- Unsigned ONLY
divModBounds :: [Prop] -> Err [SMTEntry]
divModBounds props = do
  let allBounds = concatMap (foldProp collectDivMod []) props
  if null allBounds then pure []
  else do
    assertions <- mapM mkAssertion allBounds
    pure $ (SMTComment "division/modulo bounds") : assertions
  where
    collectDivMod :: Expr a -> [(Builder, Expr EWord, Expr EWord)]
    collectDivMod = \case
      T.Div a b  -> [("abst_evm_bvudiv", a, b)]
      T.Mod a b  -> [("abst_evm_bvurem", a, b)]
      _        -> []

    mkAssertion :: (Builder, Expr EWord, Expr EWord) -> Err SMTEntry
    mkAssertion (fname, a, b) = do
      aenc <- exprToSMTAbst a
      benc <- exprToSMTAbst b
      let result = "(" <> fname `sp` aenc `sp` benc <> ")"
      pure $ SMTCommand $ "(assert (bvule " <> result `sp` aenc <> "))"

data DivModOp = IsDiv | IsMod
  deriving (Eq, Ord)

data DivOpKind = Div | SDiv | Mod | SMod
  deriving (Eq, Ord)

type DivOp = (DivOpKind, Expr EWord, Expr EWord)

data AbsKey
  = UnsignedAbsKey (Expr EWord) (Expr EWord) DivModOp
  | SignedAbsKey   (Expr EWord) (Expr EWord) DivModOp
  deriving (Eq, Ord)

isSigned :: DivOpKind -> Bool
isSigned SDiv = True
isSigned SMod = True
isSigned _     = False

isDiv :: DivOpKind -> Bool
isDiv Div  = True
isDiv SDiv = True
isDiv _     = False

divModOp :: DivOpKind -> DivModOp
divModOp k = if isDiv k then IsDiv else IsMod

absKey :: DivOp -> AbsKey
absKey (kind, a, b)
  | not (isSigned kind) = UnsignedAbsKey a b (divModOp kind)
  | otherwise           = SignedAbsKey a b (divModOp kind)

-- | Declare abs_a, abs_b, and core result variables for a signed group.
declareAbs :: Int -> Expr EWord -> Expr EWord -> Builder -> Err ([SMTEntry], (Builder, Builder))
declareAbs groupIdx firstA firstB coreName = do
  aenc <- exprToSMTAbst firstA
  benc <- exprToSMTAbst firstB
  let absAEnc = smtAbsolute aenc
      absBEnc = smtAbsolute benc
      absAName = fromString $ "abs_a_" <> show groupIdx
      absBName = fromString $ "abs_b_" <> show groupIdx
  let decls = [ SMTCommand $ "(declare-const" `sp` absAName `sp` "(_ BitVec 256))"
              , SMTCommand $ "(declare-const" `sp` absBName `sp` "(_ BitVec 256))"
              , SMTCommand $ "(declare-const" `sp` coreName `sp` "(_ BitVec 256))"
              , SMTCommand $ "(assert (=" `sp` absAName `sp` absAEnc <> "))"
              , SMTCommand $ "(assert (=" `sp` absBName `sp` absBEnc <> "))"
              ]
  pure (decls, (absAName, absBName))

-- | Ground axioms: abstract div/mod = concrete bvudiv/bvurem, grouped by operands.
divModGroundAxioms :: [Prop] -> Err [SMTEntry]
divModGroundAxioms props = do
  let allDivMods = nubOrd $ concatMap (foldProp collectDivMod []) props
  if null allDivMods then pure []
  else do
    let groups = groupBy (\a b -> absKey a == absKey b) $ sortBy (comparing absKey) allDivMods
        indexedGroups = zip [0..] groups
    entries <- concat <$> mapM (uncurry mkGroupAxioms) indexedGroups
    let links = mkCongruenceLinks indexedGroups
    pure $ (SMTComment "division/modulo ground-instance axioms") : entries <> links
  where
    collectDivMod :: forall a . Expr a -> [DivOp]
    collectDivMod = \case
      T.Div a b  -> [(Div, a, b)]
      T.SDiv a b -> [(SDiv, a, b)]
      T.Mod a b  -> [(Mod, a, b)]
      T.SMod a b -> [(SMod, a, b)]
      _        -> []

    mkGroupAxioms :: Int -> [DivOp] -> Err [SMTEntry]
    mkGroupAxioms _ [] = pure []
    mkGroupAxioms groupIdx ops@((firstKind, firstA, firstB) : _) = do
      let isDiv' = isDiv firstKind
          op = if isDiv' then "bvudiv" else "bvurem"
          coreName = op <> (fromString $ "_" <> show groupIdx)

      if not (isSigned firstKind)
      then mapM (mkUnsignedAxiom coreName) ops
      else do
        (decls, (absAName, absBName)) <- declareAbs groupIdx firstA firstB coreName
        let coreEnc = smtZeroGuard absBName $ "(" <> op `sp` absAName `sp` absBName <> ")"

        let coreAssert = SMTCommand $ "(assert (=" `sp` coreName `sp` coreEnc <> "))"
        axioms <- mapM (mkSignedAxiom coreName) ops
        pure $ decls <> [coreAssert] <> axioms

-- | Assert abstract(a,b) = concrete bvudiv/bvurem(a,b).
mkUnsignedAxiom :: Builder -> DivOp -> Err SMTEntry
mkUnsignedAxiom _coreName (kind, a, b) = do
  aenc <- exprToSMTAbst a
  benc <- exprToSMTAbst b
  let fname = if kind == Div then "abst_evm_bvudiv" else "abst_evm_bvurem"
      abstract = "(" <> fname `sp` aenc `sp` benc <> ")"
      op = if kind == Div then "bvudiv" else "bvurem"
      concrete = smtZeroGuard benc $ "(" <> op `sp` aenc `sp` benc <> ")"
  pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

-- | Assert abstract(a,b) = signed result derived from unsigned core.
mkSignedAxiom :: Builder -> DivOp -> Err SMTEntry
mkSignedAxiom coreName (kind, a, b) = do
  aenc <- exprToSMTAbst a
  benc <- exprToSMTAbst b
  let fname = if isDiv kind then "abst_evm_bvsdiv" else "abst_evm_bvsrem"
      abstract = "(" <> fname `sp` aenc `sp` benc <> ")"
      concrete = if isDiv kind
                 then smtSdivResult aenc benc coreName
                 else smtSmodResult aenc benc coreName
  pure $ SMTCommand $ "(assert (=" `sp` abstract `sp` concrete <> "))"

-- | Assert props using shift-based bounds to avoid bvudiv when possible.
assertPropsShiftBounds :: Config -> [Prop] -> Err SMT2
assertPropsShiftBounds conf ps = do
  let mkBase s = assertPropsHelperWith AbstractDivision s divModAbstractDecls
  base <- if not conf.simp then mkBase False ps
          else mkBase True (decompose conf ps)
  bounds <- divModBounds ps
  shiftBounds <- divModShiftBounds ps
  pure $ base
      <> SMT2 (SMTScript bounds) mempty mempty
      <> SMT2 (SMTScript shiftBounds) mempty mempty

isMod :: DivOpKind -> Bool
isMod Mod  = True
isMod SMod = True
isMod _     = False

-- | Shift-based bound axioms for div/mod with SHL dividends.
divModShiftBounds :: [Prop] -> Err [SMTEntry]
divModShiftBounds props = do
  let allDivs = nubBy eqDivOp $ concatMap (foldProp collectDivOps []) props
  if null allDivs then pure []
  else do
    let groups = groupBy (\a b -> absKey a == absKey b)
               $ sortBy (comparing absKey) allDivs
        indexedGroups = zip [0..] groups
    entries <- concat <$> mapM (uncurry mkGroupShiftAxioms) indexedGroups
    let links = mkCongruenceLinks indexedGroups
    pure $ (SMTComment "division/modulo shift-bound axioms (no bvudiv)") : entries <> links
  where
    collectDivOps :: forall a . Expr a -> [DivOp]
    collectDivOps = \case
      T.Div a b  -> [(Div, a, b)]
      T.SDiv a b -> [(SDiv, a, b)]
      T.Mod a b  -> [(Mod, a, b)]
      T.SMod a b -> [(SMod, a, b)]
      _        -> []

    eqDivOp :: DivOp -> DivOp -> Bool
    eqDivOp (k1, a1, b1) (k2, a2, b2) =
      k1 == k2 && a1 == a2 && b1 == b2

    -- | Extract shift amount k from SHL(k, _) or power-of-2 literals.
    extractShift :: Expr EWord -> Maybe W256
    extractShift (SHL (Lit k) _) = Just k
    extractShift (Lit n) | n > 0, n .&. (n - 1) == 0 = Just (fromIntegral $ countTrailingZeros n)
    extractShift _ = Nothing

    mkGroupShiftAxioms :: Int -> [DivOp] -> Err [SMTEntry]
    mkGroupShiftAxioms _ [] = pure []
    mkGroupShiftAxioms groupIdx ops@((firstKind, firstA, firstB) : _) = do
      let isDiv' = not (isMod firstKind)
          prefix = if isDiv' then "udiv" else "urem"
          coreName = fromString $ prefix <> "_" <> show groupIdx

      if not (isSigned firstKind) then do
        -- Unsigned: use concrete bvudiv/bvurem directly
        mapM (mkUnsignedAxiom coreName) ops
      else do
        (decls, (absAName, absBName)) <- declareAbs groupIdx firstA firstB coreName

        let shiftBounds = case (isDiv', extractShift firstA) of
              (True, Just k) ->
                let kLit = wordAsBV k
                    threshold = "(bvshl (_ bv1 256) " <> kLit <> ")"
                    shifted = "(bvlshr" `sp` absAName `sp` kLit <> ")"
                in [ SMTCommand $ "(assert (=> (=" `sp` absBName `sp` zero <> ") (=" `sp` coreName `sp` zero <> ")))"
                   , SMTCommand $ "(assert (bvule" `sp` coreName `sp` absAName <> "))"
                   , SMTCommand $ "(assert (=> (bvuge" `sp` absBName `sp` threshold <> ") (bvule" `sp` coreName `sp` shifted <> ")))"
                   , SMTCommand $ "(assert (=> (and (bvult" `sp` absBName `sp` threshold <> ") (distinct " `sp` absBName `sp` zero <> ")) (bvuge" `sp` coreName `sp` shifted <> ")))"
                   ]
              _ ->
                -- No shift info: overapproximate (only UNSAT is sound)
                [ SMTCommand $ "(assert (=> (=" `sp` absAName `sp` zero <> ") (=" `sp` coreName `sp` zero <> ")))"
                , SMTCommand $ "(assert (bvule" `sp` coreName `sp` absAName <> "))"
                ]
        axioms <- mapM (mkSignedAxiom coreName) ops
        pure $ decls <> shiftBounds <> axioms

-- | Congruence: if two signed groups have equal abs inputs, their results are equal.
mkCongruenceLinks :: [(Int, [DivOp])] -> [SMTEntry]
mkCongruenceLinks indexedGroups =
  let signedDivGroups = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups , k == SDiv]
      signedModGroups = [(i, ops) | (i, ops@((k,_,_):_)) <- indexedGroups , k == SMod]
  in    concatMap (mkPairLinks "udiv") (allPairs signedDivGroups)
     <> concatMap (mkPairLinks "urem") (allPairs signedModGroups)
  where
    allPairs xs = [(a, b) | a <- xs, b <- xs, fst a < fst b]
    mkPairLinks prefix' ((i, _), (j, _)) =
      let absAi = fromString $ "abs_a_" <> show i
          absBi = fromString $ "abs_b_" <> show i
          absAj = fromString $ "abs_a_" <> show j
          absBj = fromString $ "abs_b_" <> show j
          coreI = fromString $ prefix' <> "_" <> show i
          coreJ = fromString $ prefix' <> "_" <> show j
      in [ SMTCommand $ "(assert (=> "
            <> "(and (=" `sp` absAi `sp` absAj <> ") (=" `sp` absBi `sp` absBj <> "))"
            <> "(=" `sp` coreI `sp` coreJ <> ")))" ]

-- | (ite (= divisor 0) 0 result)
smtZeroGuard :: Builder -> Builder -> Builder
smtZeroGuard divisor nonZeroResult =
  "(ite (=" `sp` divisor `sp` zero <> ")" `sp` zero `sp` nonZeroResult <> ")"

-- | |x| as SMT.
smtAbsolute :: Builder -> Builder
smtAbsolute x = "(ite (bvsge" `sp` x `sp` zero <> ")" `sp` x `sp` "(bvsub" `sp` zero `sp` x <> "))"

-- | -x as SMT.
smtNeg :: Builder -> Builder
smtNeg x = "(bvsub" `sp` zero `sp` x <> ")"

-- | True if a and b have the same sign.
smtSameSign :: Builder -> Builder -> Builder
smtSameSign a b = "(=" `sp` "(bvslt" `sp` a `sp` zero <> ")" `sp` "(bvslt" `sp` b `sp` zero <> "))"

-- | x >= 0.
smtIsNonNeg :: Builder -> Builder
smtIsNonNeg x = "(bvsge" `sp` x `sp` zero <> ")"

-- | sdiv(a,b) from udiv(|a|,|b|): negate result if signs differ.
smtSdivResult :: Builder -> Builder -> Builder -> Builder
smtSdivResult aenc benc udivResult =
  smtZeroGuard benc $
  "(ite" `sp` smtSameSign aenc benc `sp` udivResult `sp` smtNeg udivResult <> ")"

-- | smod(a,b) from urem(|a|,|b|): result sign matches dividend.
smtSmodResult :: Builder -> Builder -> Builder -> Builder
smtSmodResult aenc benc uremResult =
  smtZeroGuard benc $
  "(ite" `sp` smtIsNonNeg aenc `sp` uremResult `sp` smtNeg uremResult <> ")"
