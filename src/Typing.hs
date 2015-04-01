{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DefaultSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Typing where

import Prelude ()
import Util.MyPrelude
import Util.PrettyM
import Syntax
import Substitution
import Names
import TcMonad
import Eval

import qualified Data.Sequence as Seq

--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------

-- make sure actual/expected arguments stay in the right order
{-
data Swapped = NotSwapped | Swapped deriving (Eq)
swapped :: Swapped -> (a -> a -> b) -> (a -> a -> b)
swapped NotSwapped f = f
swapped NotSwapped f = f
-}
type Swapped = (forall a b. (a -> a -> b) -> (a -> a -> b))
{-
data UnifySide = LeftExpected | RightExpected
swapSide :: UnifySide -> UnifySide
swapSide LeftExpected = RightExpected
swapSide RightExpected = LeftExpected
-}

-- | Verify that a meta doesn't occur in an expression
occursCheck :: MetaVar -> Exp -> TcM ()
occursCheck mv (Meta mv' _) | mv == mv' = throwError =<< text "Occurs check failed"
occursCheck mv x = traverseChildren_ (occursCheck mv) x

-- | Set a unification variable
-- Doesn't verify types
unifyMeta, unifyMeta' :: Swapped -> MetaVar -> Seq Exp -> Exp -> TcM Exp
unifyMeta swapped mv args y = unifyMeta' swapped mv args =<< evalMetas y
unifyMeta' _ mv args (Meta mv' args') | mv' == mv =
  Meta mv <$> sequenceA (Seq.zipWith unify args args')
unifyMeta' swapped mv args y = do
  mx <- metaValue mv args
  case mx of
    Just x -> swapped unify x y -- x already has a value, unify with that
    Nothing -> case unsubstN args y of
        Nothing -> throwError =<< text "Variables not in scope of meta"
        Just y' -> do
          -- perform occurs check: y' must not contain mv
          occursCheck mv y
          modifyMetaVar mv $ \val -> val { mvValue = Just y' }
          return y

--unifyLevelMeta :: LevelMetaVar -> Seq Exp -> Exp -> TcM Exp

unifyLevels :: Level -> Level -> TcM Level
unifyLevels ls = undefined

-- | Unify two expressions.
-- requires that the expressions have the same type
-- does not assume that they are in normal form
unify :: Exp -> Exp -> TcM Exp
unify x y =
  unify' x y -- first try to unify without evaluation
  `catchError` \err -> do
    x' <- eval WHNF x
    y' <- eval WHNF y
    if x /= x' || y /= y'
      then unify' x' y' `catchError` \_ -> throwError err
      else throwError err

-- | Unify two expressions that are in WHNF (or that we assume to have equal heads).
-- The left is the 'actual' type (of an argument e.g.),
-- the right is the 'expected' type (from a typesig, or applied function)
-- Optionally a value of the actual type may be passed in.
-- It will be applied to hidden arguments or wrapped in hidden lams/pairs as needed
unify' :: Exp -> Exp -> TcM Exp
unify' (Set i) (Set i') = Set <$> unifyLevels i i'
unify' (Proj p x) (Proj p' x') | p == p' = Proj p <$> unify' x x'
unify' (App x (Arg h y)) (App x' (Arg h' y')) | h == h' = App <$> unify' x x' <*> (Arg h <$> unify' y y')
unify' (Meta x args) y = unifyMeta id   x args y
unify' y (Meta x args) = unifyMeta flip x args y
unify' x y | x == y = return x
unify' x y = do
  throwError =<< text "Failed to unify" <+> ppr 11 x <+> text "with" <+> ppr 11 y

--unify' (Just valX) x (Pi (Arg Hidden u) v) =

-- | Unify x with (Set _)
unifySet :: Exp -> TcM Level
unifySet (Set i) = pure i
unifySet x = do
  i <- freshMetaLevel
  _ <- unify x (Set i)
  evalLevel i

-- | Unify x with (Binder b (Arg h _) _)
unifyBinder :: Binder -> Hiding -> Exp -> TcM (Exp, Bound Exp)
unifyBinder b h (Binder b' (Arg h' x) y) | b == b' && h == h' = return (x,y)
unifyBinder b h xy = do
  x <- freshMetaSet
  y <- Bound "" <$> localBound (unnamed x) freshMetaSet
  Binder _ (Arg _ x') y' <- unify xy (Binder b (Arg h x) y)
  return (x',y')

-- To handle hidden arguments
--   unify (Pi Hidden x y) (Set _)
--   unify (Pi Hidden x y) (Pi Visible _ _)
--   unify (Si Hidden x y) _

-- Apply x of type ty to all expected hidden arguments.
applyHidden :: Exp -> Exp -> TcM Exp
applyHidden x (Pi (Arg Hidden u) v) = do
  arg <- freshMeta u
  let x'  = App x (hidden arg)
  let ty' = substBound v arg
  applyHidden x' ty'
applyHidden x (Si (Arg Hidden _) v) = do
  let x'  = Proj (hidden Proj2) x
  let ty' = substBound v (Proj (hidden Proj1) x)
  applyHidden x' ty'
applyHidden x _ty = pure x

{-
-- Ensure that x of type ty 
wrapHidden
-}

--------------------------------------------------------------------------------
-- Typing
--------------------------------------------------------------------------------

-- Type checking and type inference
-- returns (expression, its type)
-- For typechecking, the argument must be well-typed, of type Set _
tc :: Maybe Exp -> Exp -> TcM (Exp,Exp)

tc Nothing (Var i) = do
  ty <- boundType i
  return (Var i, namedValue ty)
tc Nothing (Free x) = do
  ty <- freeType x
  return (Free x, ty)
tc Nothing (Proj p x) = do
  (x',x_ty) <- tc Nothing x
  (ty1,ty2) <- unifyBinder SiB (argHiding p) x_ty
  case argValue p of
    Proj1 -> return (Proj p x', ty1)
    Proj2 -> return (Proj p x', substBound ty2 (Proj (Proj1<$p) x'))
tc Nothing Blank = do
  ty <- freshMetaSet
  tc (Just ty) Blank
tc (Just ty) Blank = do
  x' <- freshMeta ty
  return (x',ty)
tc Nothing (Set i) = do
  i' <- evalLevel i
  return (Set i', Set (sucLevel i'))
tc Nothing (App x (Arg h y)) = do
  (x',x_ty) <- tc Nothing x
  (ty1,ty2) <- unifyBinder PiB h x_ty
  (y',_) <- tc (Just ty1) y
  return (App x' (Arg h y'), substBound ty2 y')
tc Nothing (TypeSig x y) = do
  (y',l) <- tcType y
  tc (Just y') x
tc Nothing (Lam (Arg h x) (Bound n y)) = do
  (x',_) <- tcType x
  (y',t) <- localBound (named n x') (tc Nothing y)
  return (Lam (Arg h x') (Bound n y'), Pi (Arg h x') (Bound n y))
tc Nothing (Binder b (Arg h x) (Bound n y)) = do -- Pi or Sigma
  (x',lx) <- tcType x
  (y',ly) <- localBound (named n x') (tcType y)
  return (Binder b (Arg h x') (Bound n y'), Set (maxLevel lx ly))

tc (Just ty) x = do
  (x',ty') <- tc Nothing x
  ty'' <- unify ty ty'
  return (x',ty'')

-- check that x is a type, return its level
tcType :: Exp -> TcM (Exp, Level)
tcType x = do
  (x',l) <- tc Nothing x
  l' <- unifySet l
  return (x',l')

