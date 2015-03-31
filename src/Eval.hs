{-# LANGUAGE PatternSynonyms #-}
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
data NfStrategy = WHNF | NF | MetaOnly | OneStep
  deriving (Eq)

eval :: NfStrategy -> Exp -> TcM Exp
eval _ (Var x) = pure $ Var x
eval _ (Set i) = pure $ Set i
eval _ (Free x) = pure $ Free x
eval s (TypeSig x _ty) = eval s x
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

evalMore :: NfStrategy -> Exp -> TcM Exp
evalMore OneStep x = pure x
evalMore s x = eval s x

evalApp :: NfStrategy -> Exp -> Arg Exp -> TcM Exp
evalApp s (Lam _ x) y | s /= MetaOnly = eval s $ subst1 (argValue y) (boundBody x)
evalApp _ x y = pure $ App x y

evalPair :: NfStrategy -> Proj -> Exp -> TcM Exp
evalPair s Proj1 (Pair x _y _) | s /= MetaOnly = eval s x
evalPair s Proj2 (Pair _x y _) | s /= MetaOnly = eval s y
evalPair _ p x = pure $ Proj p x

