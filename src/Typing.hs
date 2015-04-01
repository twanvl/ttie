{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DefaultSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
module Typing where

import Prelude ()
import Util.MyPrelude
import Util.Pretty
import Syntax
import Substitution
import Names
import TcMonad
import Eval

--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------

data UnifySide = LeftExpected | RightExpected
swapSide :: UnifySide -> UnifySide
swapSide LeftExpected = RightExpected
swapSide RightExpected = LeftExpected

unify :: Exp -> Exp -> TcM Exp
unify (Proj p x) (Proj q y) | p == q = Proj p <$> unify x y
unify x y | x == y = return x
unify x y = do
  throwError $ text "Failed to unify"

--------------------------------------------------------------------------------
-- Typing
--------------------------------------------------------------------------------

-- Type checking and type inference
-- returns (expression, its type)
-- For typechecking, the argument must be well-typed and of type Set _
tc :: Maybe Exp -> Exp -> TcM (Exp,Exp)

tc Nothing (Var i) = do
  ty <- tcGetVar i
  return (Var i, namedValue ty)
tc Nothing (Free x) = do
  ty <- tcFreeType x
  return (Free x, ty)
tc Nothing (Proj p x) = do
  (x',x_ty) <- tc Nothing x
  (ty1,ty2) <- unifySi x_ty
  case p of
    Proj1 -> return (Proj p x', ty1)
    Proj2 -> return (Proj p x', substBound ty2 (Proj Proj1 x'))
tc Nothing Blank = do
  ty <- freshMetaSet
  tc (Just ty) Blank
tc (Just ty) Blank = do
  x' <- freshMeta ty
  return (x',ty)
tc Nothing (Set i) = do
  i' <- evalLevel i
  return (Set i', Set (sucLevel i'))

tc (Just ty) x = do
  (x,ty') <- tc Nothing x
  ty'' <- unify ty ty'
  return (x,ty'')

