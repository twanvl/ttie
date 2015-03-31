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

{-
eval :: EvalStrategy -> Exp -> TcM Exp
eval _ (Var x) = pure $ Var x
eval _ (Set i) = pure $ Set i
eval _ (Free x) = pure $ Free x
eval s (TypeSig x _ty) = evalMore s x
eval s (App x y) = join $ evalApp s <$> eval s x <*> traverse (eval s) y
eval s (Proj p x) = join $ evalPair s p <$> eval s x
eval s (Meta x xs) = do
  m <- metaValue x xs
  case m of
    Nothing -> Meta x <$> mapM (eval s) xs
    Just m' -> eval s m'
eval _ Blank = freshMetaAny
eval WHNF x = pure x
eval s (Pair x y z) = Pair <$> eval s x <*> eval s y <*> eval s z
eval s (Binder b x y) = Binder b <$> traverse (eval s) x <*> tcTraverse (argValue x) (eval s) y
-}

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
evalApp s (Lam _ x) y = evalMore s $ subst1 (argValue y) (boundBody x)
evalApp _ x y = pure $ App x y

evalProj :: EvalStrategy -> Proj -> Exp -> TcM Exp
evalProj s Proj1 (Pair x _y _) = evalMore s x
evalProj s Proj2 (Pair _x y _) = evalMore s y
evalProj _ p x = pure $ Proj p x

--------------------------------------------------------------------------------
-- Evaluation in all possible locations
--------------------------------------------------------------------------------

-- | Apply a function to x and all its children (independently)
everywhere :: (MonadBound Exp f, Alternative f) => (Exp -> f Exp) -> Exp -> f Exp
everywhere f x = f x <|> traverseChildren (everywhere f) x

-- Compose, but with the Alternative instance using g instead of f
newtype Compose' f g a = Compose' { getCompose' :: f (g a) }

instance (Functor f, Functor g) => Functor (Compose' f g) where
  fmap f (Compose' x) = Compose' (fmap (fmap f) x)

instance (Applicative f, Applicative g) => Applicative (Compose' f g) where
  pure x = Compose' (pure (pure x))
  Compose' f <*> Compose' x = Compose' ((<*>) <$> f <*> x)

instance (Applicative f, Alternative g) => Alternative (Compose' f g) where
  empty = Compose' (pure empty)
  Compose' x <|> Compose' y = Compose' ((<|>) <$> x <*> y)

instance (MonadBound Exp f, MonadBound Exp g) => MonadBound Exp (Compose' f g) where
  localBound x (Compose' y) = Compose' (localBound x (localBound x y))

-- Track ways to change part of an expression
data Change a = Change { changeOrig :: a, changeNew :: [a] }
  deriving (Functor)
instance Applicative Change where
  pure x = Change x []
  Change x xs <*> Change y ys = Change (x y) (map ($y) xs ++ map x ys)
instance Alternative Change where
  empty = error "only (<|>)"
  Change x xs <|> Change _ ys = Change x (xs ++ ys)
instance MonadBound Exp Change where
  localBound _ = id

tryEvalHere :: Exp -> TcM (Change Exp)
tryEvalHere x = do
  x' <- eval OneStep x
  return $ Change x [x' | x'/=x]

-- all possible ways to take a single evaluation step
-- used to test confluence
evalEverywhere :: Exp -> TcM [Exp]
evalEverywhere x = changeNew <$> getCompose' (everywhere (Compose' . tryEvalHere) x)

