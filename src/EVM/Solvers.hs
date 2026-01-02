{- |
    Module: EVM.Solvers
    Description: Solver orchestration
-}
module EVM.Solvers
(
  checkSatWithProps, collectSolutions, withSolvers, Solver(..), SolverGroup
)
where


import EVM.Solvers.Internal hiding (collectSolutions)
import EVM.Solvers.Internal qualified as Internal (collectSolutions)

import EVM.Effects
import EVM.Expr (simplifyProps)
import EVM.Keccak qualified as Keccak (concreteKeccaks)
import EVM.SMT (assertProps)
import EVM.Types

import Control.Monad.IO.Class (liftIO)
import Data.Either (isLeft)
import Data.Set (toList)

collectSolutions :: App m => SolverGroup -> Expr EWord -> Prop -> Int -> m (Maybe [W256])
collectSolutions sg symExpr conds numBytes = do
  conf <- readConfig
  let smtOrError = assertProps conf [(PEq (Var "multiQueryVar") symExpr) .&& conds]
  case smtOrError of
    Left _ -> pure Nothing
    Right smt -> liftIO $ Internal.collectSolutions sg smt $ MultiSol { maxSols = conf.maxWidth , numBytes = numBytes , var = "multiQueryVar" }

checkSatWithProps :: App m => SolverGroup -> [Prop] -> m (SMTResult)
checkSatWithProps sg props = do
  conf <- readConfig
  let psSimp = if conf.simp then simplifyProps props else props
  if psSimp == [PBool False] then pure Qed
  else do
    let concreteKeccaks = fmap (\(buf,val) -> PEq (Lit val) (Keccak buf)) (toList $ Keccak.concreteKeccaks props)
    let smt2 = assertProps conf (if conf.simp then psSimp <> concreteKeccaks else psSimp)
    if isLeft smt2 then pure $ Error $ getError smt2
    else liftIO $ checkSat sg (Just props) $ getNonError smt2
