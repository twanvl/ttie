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
  ,("x", pe "A"),("y", pe "A")
  ,("f", pe "A -> B")
  ,("Nat", pe "Set")
  ,("zero", pe "Nat")
  ,("suc", pe "Nat -> Nat")
  ]

testCtx :: TcCtx
testCtx = emptyCtx
  { ctxFreeType = testNames
  }

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
  ,"refl (x,x)"
  ,"i12"
  --,"(\\f g x -> f (g x)) : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)"
  ]

-- expressions that shouldn't typecheck
badExpressions :: [String]
badExpressions =
  ["Set : Set"
  ,"f (f x)"
  ,"notInScope"
  ,"\\x. x"
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
    showError $ runTcM testCtx $ evalAllMetas =<< tc Nothing x
  -- and the modified expression should yield the same type
  testPart "Type inference of expanded expression" $ do
    xty' <- showError $ runTcM testCtx $ evalAllMetas =<< tc Nothing x'
    assertEqual "Should be equal" (x',ty) xty'
  -- and we should also be able to typecheck it
  testPart "Type checking" $ do
    xty' <- showError $ runTcM testCtx $ evalAllMetas =<< tc (Just ty) x'
    assertEqual "Should be equal" (x',ty) xty'
  -- all the ways to evaluate x to normal form should give the same result
  testPart "Evaluation" $ do
    return ()
  return ""

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

