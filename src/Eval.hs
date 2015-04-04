{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
module Eval where

import Prelude ()
import Util.MyPrelude
import Util.Pretty
import Syntax
import Substitution
import Names
import TcMonad

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

type NfExp = Exp
data EvalStrategy = WHNF | NF | MetaOnly | OneStep
  deriving (Eq)

eval :: EvalStrategy -> Exp -> TcM Exp
eval WHNF x@(Pair _ _ _) = pure x
eval WHNF x@(Binder _ _ _) = pure x
eval s (Meta x xs) = evalMeta s x xs
eval MetaOnly x = pure x
eval s (TypeSig x _ty) = evalMore s x
eval s x = evalHere s =<< traverseChildren (evalMore s) x

evalHere :: EvalStrategy -> Exp -> TcM Exp
evalHere s (TypeSig x _ty) = evalMore s x
evalHere s (App x y) = evalApp s x y
evalHere s (Proj x y) = evalProj s x y
evalHere _ x = pure x

evalMore :: EvalStrategy -> Exp -> TcM Exp
evalMore OneStep x = pure x
evalMore s x = eval s x

evalMeta :: EvalStrategy -> MetaVar -> Seq Exp -> TcM Exp
evalMeta s x xs = do
  m <- metaValue x xs
  case m of
    Nothing -> Meta x <$> mapM (eval s) xs
    Just m' -> eval s m'

evalApp :: EvalStrategy -> Exp -> Arg Exp -> TcM Exp
evalApp s (Lam _ x) y = evalMore s $ substBound x (argValue y)
evalApp _ x y = pure $ App x y

evalProj :: EvalStrategy -> Arg Proj -> Exp -> TcM Exp
evalProj s (Arg _ Proj1) (Pair x _y _) = evalMore s (argValue x)
evalProj s (Arg _ Proj2) (Pair _x y _) = evalMore s y
evalProj _ p x = pure $ Proj p x

--------------------------------------------------------------------------------
-- Evaluation in all possible locations
--------------------------------------------------------------------------------

-- | Apply a function to x and all its children (independently), collect results
everywhere :: (MonadBound Exp f, Alternative g) => (Exp -> f (g Exp)) -> Exp -> f (g Exp)
everywhere f x = (<|>) <$> f x <*> getCompose (traverseChildren (Compose . everywhere f) x)

-- Track ways to change part of an expression
data Change a = Change { changeOrig :: a, changeNew :: [a] }
  deriving (Functor)
instance Applicative Change where
  pure x = Change x []
  Change x xs <*> Change y ys = Change (x y) (map ($y) xs ++ map x ys)
instance Alternative Change where
  empty = error "only (<|>)"
  Change x xs <|> Change _ ys = Change x (xs ++ ys)

tryEvalHere :: Exp -> TcM (Change Exp)
tryEvalHere x = do
  x' <- eval OneStep x
  return $ Change x [x' | x'/=x]

-- all possible ways to take a single evaluation step
-- used to test confluence
evalEverywhere :: Exp -> TcM [Exp]
evalEverywhere x = changeNew <$> everywhere tryEvalHere x

