{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DefaultSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Tests where

import Prelude ()
import Util.MyPrelude
import Util.PrettyM
import Util.Parser
import Syntax
import Substitution
import Names
import TcMonad
import Typing
import Eval

import qualified Data.Map as Map
import Data.Typeable
import Data.String

import Test.Tasty
--import Test.Tasty.HUnit
import Test.Tasty.Providers
--import Test.HUnit hiding (Test)
import qualified Control.Exception as E

--------------------------------------------------------------------------------
-- Environment with some names
--------------------------------------------------------------------------------

testNames :: Map Name Exp
testNames = Map.fromList
  [("A", pe "Set")
  ,("B", pe "Set")
  ,("x", pe "A"),("y", pe "A"),("xy", pe "Eq A x y")
  ,("f", pe "A -> B")
  ,("B'", pe "A -> Set")
  ,("f'", pe "(x:A) -> B' x")
  ,("ab", pe "Eq Set A B")
  ,("Nat", pe "Set")
  ,("zero", pe "Nat")
  ,("suc", pe "Nat -> Nat")
  ]
  -- "Nat", pe "Set", pe "x:data{zero;suc} * case x of {zero -> data{unit}; suc -> Nat}"
  -- "Nat", pe "Set", pe "data{zero:Unit;suc:Nat}"
  -- "zero", , pe "con{zero}"

testCtx :: TcCtx
testCtx = emptyCtx
  { ctxFreeType = testNames
  }

testTcM :: EvalAllMetas a => TcM a -> a
testTcM x = case runTcM testCtx (x >>= evalAllMetas) of
  Left e -> error (show e)
  Right y -> y

testTcM' :: EvalAllMetas a => TcM a -> (a,Doc)
testTcM' x = testTcM ((,) <$> x <*> dumpMetas)

--------------------------------------------------------------------------------
-- Expressions to test
--------------------------------------------------------------------------------

-- expressions that should typecheck
goodExpressions :: [String]
goodExpressions =
  ["\\(x:A). x"
  ,"proj1 (x,y)"
  ,"proj2 (x,y)"
  ,"f x"
  ,"{A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)"
  ,"(\\{u} x -> x) : {A : Set} -> (A -> A)"
  ,"(\\{A} {B} f x -> f x) : {A B : Set} -> (A -> B) -> (A -> B)"
  ,"(\\{A} {B} {C} f g x -> f (g x)) : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)"
  ,"(\\f g x -> f (g x)) : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)"
  ,"refl (x,x)"
  ,"i12"
  ,"refl_i (\\(x:(refl Nat)^i) -> x)"
  ,"proj2 ({x} , x , f) x"
  -- OTT
  {-
  ,"proj1 (refl (x,y))"
  ,"(refl f') {_} {_} (refl x)"
  ,"(refl f') xy"
  ,"(\\x y -> tt) : (x y : Unit) -> Eq _ x y"
  -}
  ,"(\\xx' -> refl_i (f xx'^i)) : forall {x x'}. Eq A x x' -> Eq _ (f x) (f x')"
  -- casts
  ,"{-subst-} (\\P {x} {y} xy px -> fw_i (P xy^i) px)"
   ++": {A : Set} -> (P : A -> Set) -> {x y : A} -> Eq _ x y -> P x -> P y"
  ,"{-jay-type-} {A : Set} -> {x : A} -> (P : (y : A) -> Eq A x y -> Set) -> {y : A} -> (xy : Eq A x y) -> P x (refl x) -> P y xy"
  ,"{-bw-fw-} (\\x -> refl_i (cast_j ab^j i i1 (cast_j ab^j i1 i x)))"
   ++" : forall x. Eq _ x (bw_i ab^i (fw_i ab^i x))"
  ,"{-eq-fw-} (\\x -> refl_i (cast_j ab^j i1 i x))"
   ++" : forall x. Eq_i ab^i x (fw_i ab^i x)"
  ,"(\\{A} {x} P {y} xy px -> fw_i (P xy^i (cast_j (Eq A x xy^j) i1 i (refl x))) px) :" ++
   "{A : Set} -> {x : A} -> (P : (y : A) -> Eq A x y -> Set) -> {y : A} -> (xy : Eq A x y) -> P x (refl x) -> P y xy"
  ]

-- expressions that shouldn't typecheck
badExpressions :: [String]
badExpressions =
  ["Set : Set"
  ,"f (f x)"
  ,"notInScope"
  ,"\\x. x"
  ,"(refl f) x"
  ,"f (refl x)"
  ]

--------------------------------------------------------------------------------
-- Simple test framework
--------------------------------------------------------------------------------

showError :: Show err => Either err a -> Either String a
showError = either (Left . show) Right

testPart :: String -> Either String a -> Either String a
testPart part = either (Left . (part ++) . ("\n" ++)) Right

type MyAssertion = Either String ()

assert :: String -> Bool -> MyAssertion
assert msg False = Left $ msg
assert _   True = return ()

assertEqual :: (Eq a, Show a) => String -> a -> a -> MyAssertion
assertEqual msg x y = assert (unlines [msg,"  "++show x,"  "++show y]) (x == y)

assertFailed :: Show a => String -> Either err a -> MyAssertion
assertFailed _   (Left _) = Right ()
assertFailed msg (Right a) = Left (msg ++ "\n" ++ show a)

newtype TestCase = TestCase (Either String String)
  deriving Typeable

testCase :: TestName -> MyAssertion -> TestTree
testCase name = testCaseInfo name . ("" <$)

testCaseInfo :: TestName -> Either String String -> TestTree
testCaseInfo name = singleTest name . TestCase

instance IsTest TestCase where
  testOptions = return []
  run _ (TestCase (Left e))     _ = return $ testFailed e
  run _ (TestCase (Right info)) _ = return $ testPassed info

--------------------------------------------------------------------------------
-- Test of parser and typechecker
--------------------------------------------------------------------------------

myTestTcM :: (EvalAllMetas a, Pretty TcM a) => TcM a -> Either String a
myTestTcM mx = showError $ runTcM testCtx $ do
  x <- mx
  evalAllMetasThrow x `annError` (text "in" <+> ppr 0 x)

testExp :: String -> Either String String
testExp xStr = do
  -- we should be able to parse the expression
  x <- testPart "Parsing" $
    showError $ runParser parseExpTop "input" xStr
  -- we should be able to pretty print and re-parse
  testPart "Pretty printer" $ do
    let xStr' = show x
    x' <- showError $ runParser parseExpTop "prety-printed" xStr'
    assertEqual "parse.ppr not identity" x x'
  -- we should be able to infer its type
  (x',ty) <- testPart "Type inference" $
    myTestTcM $ tc Nothing x
  -- and the modified expression should yield the same type
  testPart "Type inference of expanded expression" $ do
    (x'',ty') <- myTestTcM $ tc Nothing x'
    tyNf <- myTestTcM $ eval NF ty
    ty'Nf <- myTestTcM $ eval NF ty'
    assertEqual "Values should be equal" x' x''
    assertEqual "Types should be equal" tyNf ty'Nf
  -- and we should also be able to typecheck it
  testPart "Type checking" $ do
    xty' <- myTestTcM $ tc (Just ty) x'
    assertEqual "Should be equal" (x',ty) xty'
  -- evaluation (to normal form) should preserve typing
  xnf <- testPart "Evaluation typing" $ do
    xnf <- myTestTcM $ eval NF x'
    (_,ty') <- myTestTcM $ tc (Just ty) xnf
    -- ty and ty' should have the same normal form (we already know that they unify)
    tyNf <- myTestTcM $ eval NF ty
    ty'Nf <- myTestTcM $ eval NF ty'
    assertEqual "Should have same type in normal form" tyNf ty'Nf
    return xnf
  -- eval NF should also give a normal form
  testPart "Normal form" $ do
    xnf' <- myTestTcM $ eval NF xnf
    assertEqual "eval NF should give normal form" xnf xnf'
  -- all the ways to evaluate x to normal form should give the same result
  testPart "Evaluation" $ do
    return ()
  -- return some info
  --return ""
  tyNf <- myTestTcM $ eval NF ty
  return $ show tyNf

testBadExp :: String -> Either String ()
testBadExp xStr = do
  x <- testPart "Parsing" $
    showError $ runParser parseExpTop "input" xStr
  assertFailed "Type inference should fail" $
    myTestTcM $ tc Nothing x

--------------------------------------------------------------------------------
-- Main: testcases
--------------------------------------------------------------------------------

-- 
--splitTest :: 

tests :: TestTree
tests = testGroup "Tests"
  [ testGroup "Should pass"
    [ testCaseInfo (take 20 xStr) (testExp xStr) | xStr <- goodExpressions ]
  , testGroup "Should fail"
    [ testCase (take 20 xStr) (testBadExp xStr) | xStr <- badExpressions ]
  ]

main :: IO ()
main = defaultMain tests

