module EVM.Expr.ExprTests (tests) where

import Test.Tasty
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.HUnit

import Data.Map.Strict qualified as Map

import EVM.Expr qualified as Expr
import EVM.Types

tests :: TestTree
tests = testGroup "Expr"
  [unitTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ simplificationTests
  , constantPropagationTests
  , boundPropagationTests
  ]

simplificationTests :: TestTree
simplificationTests = testGroup "Expr-rewriting"
  [ storageTests
  , copySliceTests
  , basicSimplificationTests
  ]

storageTests :: TestTree
storageTests = testGroup "Storage tests"
  [
    testCase "read-from-sstore" $ assertEqual errorMsg
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (SStore (Lit 0x0) (Lit 0xab) (AbstractStore (LitAddr 0x0) Nothing)))
    , testCase "read-from-concrete" $ assertEqual errorMsg
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (ConcreteStore $ Map.fromList [(0x0, 0xab)]))
    , testCase "read-past-write" $ assertEqual errorMsg
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (SStore (Lit 0x1) (Var "b") (ConcreteStore $ Map.fromList [(0x0, 0xab)])))
  ]
  where errorMsg = "Storage read expression not simplified correctly"

copySliceTests :: TestTree
copySliceTests = testGroup "CopySlice tests"
  [ testCase "copyslice-simps" $ do
        let e a b =  CopySlice (Lit 0) (Lit 0) (BufLength (AbstractBuf "buff")) (CopySlice (Lit 0) (Lit 0) (BufLength (AbstractBuf "buff")) (AbstractBuf "buff") (ConcreteBuf a)) (ConcreteBuf b)
            expr1 = e "" ""
            expr2 = e "" "aasdfasdf"
            expr3 = e "9832478932" ""
            expr4 = e "9832478932" "aasdfasdf"
        assertEqual "Not full simp" (Expr.simplify expr1) (AbstractBuf "buff")
        assertEqual "Not full simp" (Expr.simplify expr2) $ CopySlice (Lit 0x0) (Lit 0x0) (BufLength (AbstractBuf "buff")) (AbstractBuf "buff") (ConcreteBuf "aasdfasdf")
        assertEqual "Not full simp" (Expr.simplify expr3) (AbstractBuf "buff")
        assertEqual "Not full simp" (Expr.simplify expr4) $ CopySlice (Lit 0x0) (Lit 0x0) (BufLength (AbstractBuf "buff")) (AbstractBuf "buff") (ConcreteBuf "aasdfasdf")
  ]
basicSimplificationTests :: TestTree
basicSimplificationTests = testGroup "Basic simplification tests"
  [ testCase "simp-readByte1" $ do
      let srcOffset = (ReadWord (Lit 0x1) (AbstractBuf "stuff1"))
          size = (ReadWord (Lit 0x1) (AbstractBuf "stuff2"))
          src = (AbstractBuf "stuff2")
          e = ReadByte (Lit 0x0) (CopySlice srcOffset (Lit 0x10) size src (AbstractBuf "dst"))
          simp = Expr.simplify e
      assertEqual "readByte simplification" simp (ReadByte (Lit 0x0) (AbstractBuf "dst"))
  , testCase "simp-max-buflength" $ do
      let simp = Expr.simplify $ Max (Lit 0) (BufLength (AbstractBuf "txdata"))
      assertEqual "max-buflength rules" simp $ BufLength (AbstractBuf "txdata")
  , testCase "simp-PLT-max" $ do
      let simp = Expr.simplifyProp $ PLT (Max (Lit 5) (BufLength (AbstractBuf "txdata"))) (Lit 99)
      assertEqual "max-buflength rules" simp $ PLT (BufLength (AbstractBuf "txdata")) (Lit 99)
  , testCase "simp-assoc-add1" $ do
      let simp = Expr.simplify $ Add (Add (Var "c") (Var "a")) (Var "b")
      assertEqual "assoc rules" simp $ Add (Var "a") (Add (Var "b") (Var "c"))
  , testCase "simp-assoc-add2" $ do
      let simp = Expr.simplify $ Add (Add (Lit 1) (Var "c")) (Var "b")
      assertEqual "assoc rules" simp $ Add (Lit 1) (Add (Var "b") (Var "c"))
  , testCase "simp-assoc-add3" $ do
      let simp = Expr.simplify $ Add (Lit 1) (Add (Lit 2) (Var "c"))
      assertEqual "assoc rules" simp $ Add (Lit 3) (Var "c")
  , testCase "simp-assoc-add4" $ do
      let simp = Expr.simplify $ Add (Lit 1) (Add (Var "b") (Lit 2))
      assertEqual "assoc rules" simp $ Add (Lit 3) (Var "b")
  , testCase "simp-assoc-add5" $ do
      let simp = Expr.simplify $ Add (Var "a") (Add (Lit 1) (Lit 2))
      assertEqual "assoc rules" simp $ Add (Lit 3) (Var "a")
  , testCase "simp-assoc-add6" $ do
      let simp = Expr.simplify $ Add (Lit 7) (Add (Lit 1) (Lit 2))
      assertEqual "assoc rules" simp $ Lit 10
  , testCase "simp-assoc-add-7" $ do
      let simp = Expr.simplify $ Add (Var "a") (Add (Var "b") (Lit 2))
      assertEqual "assoc rules" simp $ Add (Lit 2) (Add (Var "a") (Var "b"))
  , testCase "simp-assoc-add8" $ do
      let simp = Expr.simplify $ Add (Add (Var "a") (Add (Lit 0x2) (Var "b"))) (Add (Var "c") (Add (Lit 0x2) (Var "d")))
      assertEqual "assoc rules" simp $ Add (Lit 4) (Add (Var "a") (Add (Var "b") (Add (Var "c") (Var "d"))))
  , testCase "simp-assoc-mul1" $ do
      let simp = Expr.simplify $ Mul (Mul (Var "b") (Var "a")) (Var "c")
      assertEqual "assoc rules" simp $ Mul (Var "a") (Mul (Var "b") (Var "c"))
  , testCase "simp-assoc-mul2" $ do
      let simp = Expr.simplify $ Mul (Lit 2) (Mul (Var "a") (Lit 3))
      assertEqual "assoc rules" simp $ Mul (Lit 6) (Var "a")
  , testCase "simp-assoc-xor1" $ do
      let simp = Expr.simplify $ Xor (Lit 2) (Xor (Var "a") (Lit 3))
      assertEqual "assoc rules" simp $ Xor (Lit 1) (Var "a")
  , testCase "simp-assoc-xor2" $ do
      let simp = Expr.simplify $ Xor (Lit 2) (Xor (Var "b") (Xor (Var "a") (Lit 3)))
      assertEqual "assoc rules" simp $ Xor (Lit 1) (Xor (Var "a") (Var "b"))
  ]

constantPropagationTests :: TestTree
constantPropagationTests = testGroup "isUnsat-concrete-tests"
  [
    testCase "disjunction-left-false" $
    let
      t = [PEq (Var "x") (Lit 1), POr (PEq (Var "x") (Lit 0)) (PEq (Var "y") (Lit 1)), PEq (Var "y") (Lit 2)]
      propagated = Expr.constPropagate t
    in
    mustContainFalse propagated
  , testCase "disjunction-right-false" $
      let
        t = [PEq (Var "x") (Lit 1), POr (PEq (Var "y") (Lit 1)) (PEq (Var "x") (Lit 0)), PEq (Var "y") (Lit 2)]
        propagated = Expr.constPropagate t
      in
      mustContainFalse propagated
  , testCase "disjunction-both-false" $
      let
        t = [PEq (Var "x") (Lit 1), POr (PEq (Var "x") (Lit 2)) (PEq (Var "x") (Lit 0)), PEq (Var "y") (Lit 2)]
        propagated = Expr.constPropagate t
      in
      mustContainFalse propagated
  , ignoreTest $ testCase "disequality-and-equality" $
      let
        t = [PNeg (PEq (Lit 1) (Var "arg1")), PEq (Lit 1) (Var "arg1")]
        propagated = Expr.constPropagate t
      in
      mustContainFalse propagated
  , testCase "equality-and-disequality" $
      let
        t = [PEq (Lit 1) (Var "arg1"), PNeg (PEq (Lit 1) (Var "arg1"))]
        propagated = Expr.constPropagate t
      in
      mustContainFalse propagated
  ]
  where
    mustContainFalse props = assertBool "Expression must simplify to False" $ (PBool False) `elem` props

boundPropagationTests :: TestTree
boundPropagationTests =  testGroup "inequality-propagation-tests" [
  testCase "PLT-detects-impossible-constraint" $
  let
    -- x < 0 is impossible for unsigned integers
    t = [PLT (Var "x") (Lit 0)]
    propagated = Expr.constPropagate t
  in
    mustContainFalse propagated
  , testCase "PLT-overflow-check" $
      let
        -- maxLit < y is impossible
        t = [PLT (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) (Var "y")]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "PGT-detects-impossible-constraint" $
      let
        -- x > maxLit is impossible
        t = [PGT (Var "x") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "PGT-overflow-check" $
      let
        -- 0 > y is impossible
        t = [PGT (Lit 0) (Var "y")]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "inequality-conflict-detection-narrow" $
      let
        -- x < 2 && x > 5 is impossible
        t = [PLT (Var "x") (Lit 2), PGT (Var "x") (Lit 5)]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "inequality-conflict-detection-wide" $
      let
        -- x < 5 && x > 10 is impossible
        t = [PLT (Var "x") (Lit 5), PGT (Var "x") (Lit 10)]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "inequality-tight-bounds-satisfied" $
      let
        -- x >= 5 && x <= 5 and x == 5 should be consistent
        t = [PGEq (Var "x") (Lit 5), PLEq (Var "x") (Lit 5), PEq (Var "x") (Lit 5)]
        propagated = Expr.constPropagate t
      in
        mustNotContainFalse propagated
  , testCase "inequality-tight-bounds-violated" $
      let
        -- x >= 5 && x <= 5 and x != 5 should be inconsistent
        t = [PGEq (Var "x") (Lit 5), PLEq (Var "x") (Lit 5), PNeg (PEq (Var "x") (Lit 5))]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
  , testCase "inequality-with-existing-equality-consistent" $
      let
        -- x == 5 && x < 10 is consistent
        t = [PEq (Var "x") (Lit 5), PLT (Var "x") (Lit 10)]
        propagated = Expr.constPropagate t
      in
        mustNotContainFalse propagated
  , testCase "inequality-with-existing-equality-inconsistent" $
      let
        -- x == 5 && x < 5 is inconsistent
        t = [PEq (Var "x") (Lit 5), PLT (Var "x") (Lit 5)]
        propagated = Expr.constPropagate t
      in
        mustContainFalse propagated
    ]
  where
    mustContainFalse props = assertBool "Expression must simplify to False" $ (PBool False) `elem` props
    mustNotContainFalse props = assertBool "Expression must NOT simplify to False" $ (PBool False) `notElem` props