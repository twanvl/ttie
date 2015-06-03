{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms #-}
{-# LANGUAGE DefaultSignatures, ConstraintKinds #-}
module Substitution where

import Prelude ()
import Util.MyPrelude
import Util.Pretty
import Util.Parser
import Names

import qualified Data.IntMap as IM
import qualified Data.Sequence as Seq

--------------------------------------------------------------------------------
-- Substitution and friends
--------------------------------------------------------------------------------

class TraverseChildren a a => Subst a where
  var :: Int -> a
  unVar :: a -> Maybe Int

  -- traverse all variables
  mapExpM :: Applicative f => (Int -> f a) -> (a -> f a)
  mapExpM f = runDepthT 0 . go
    where
    go x = case unVar x of
      Just i  -> withDepth $ \l ->
                   if i < l
                   then pure (var i)
                   else raiseBy l <$> f (i-l)
      Nothing -> traverseChildren go x

mapExp :: Subst a => (Int -> a) -> (a -> a)
mapExp f = runIdentity . mapExpM (pure . f)

raiseBy :: Subst a => Int -> a -> a
raiseBy 0 x = x
raiseBy n (unVar -> Just x) = var (n + x)
raiseBy n x = mapExp (\i -> var (n + i)) x

-- raiseAtBy a b = raiseSubst b [var 0, var 1, var 2, .., var (a-1)]
raiseAtBy :: Subst a => Int -> Int -> a -> a
raiseAtBy m n = mapExp (\i -> if i < m then var i else var (n + i))

raiseSubsts :: Subst a => Int -> [a] -> (a -> a)
raiseSubsts n = mapExp . substsVar
  where
  substsVar []     i = var (n + i)
  substsVar (x:_)  0 = x
  substsVar (_:xs) i = substsVar xs (i - 1)

raiseSubstsM :: (Subst a, Applicative f) => Int -> [f a] -> a -> f a
raiseSubstsM n = mapExpM . substsVarM
  where
  substsVarM []     i = pure $ var (n + i)
  substsVarM (x:_)  0 = x
  substsVarM (_:xs) i = substsVarM xs (i - 1)

substs :: Subst a => [a] -> (a -> a)
substs = raiseSubsts 0

subst1 :: Subst a => a -> (a -> a)
subst1 x = substs [x]

substAt :: Subst a => Int -> a -> (a -> a)
substAt n x = mapExp substVar
  where
  substVar i | i < n     = var i
             | i == n    = x
             | otherwise = var (i-1)

substRaiseAt :: Subst a => Int -> a -> (a -> a)
substRaiseAt n x = substAt n (raiseBy n x)

substsN :: Subst a => Seq a -> (a -> a)
substsN Empty = id
substsN xs = mapExp $ \i -> if i < Seq.length xs
  then Seq.index xs i
  else var (i - Seq.length xs)

-- does a variable occur free in the given expression
varUsed :: Subst a => Int -> a -> Bool
varUsed v = getAny . getConst . mapExpM (\i -> Const . Any $ i == v)

--------------------------------------------------------------------------------
-- 'un'substitution
--------------------------------------------------------------------------------

-- | Expressing each variable of the target as an expression of the source
-- i.e. the type of meta arguments
type InvCtxMap a = Seq a

-- Expressing some variables of the source as an expression of the target
type PartialCtxMap a = IntMap a

-- Go from arguments that express each target var as a source expression 
invCtxMap :: Subst a => InvCtxMap a -> PartialCtxMap a
invCtxMap xs = IM.fromList [ (v,var i) | (i, unVar -> Just v) <- zip [0..] (toList xs) ]

unsubstN :: Subst a => InvCtxMap a -> a -> Maybe a
unsubstN xs = mapExpM $ \i -> IM.lookup i vars
  where
  vars = invCtxMap xs

-- replace all occurences of pat with (var 0)
unsubst1 :: (Eq a, Subst a) => a -> a -> a
unsubst1 pat = runIdentity . runDepthT 0 . go
  where
  go x = withDepth $ \l -> case unVar x of
     _ | x == raiseBy l pat -> pure (var l)
     Just i | i < l     -> pure (var i)
     Just i | otherwise -> pure (var (i+1))
     Nothing            -> runDepthT l $ traverseChildren go x

lowerBy :: Subst a => Int -> a -> Maybe a
lowerBy 0 = pure
lowerBy n = mapExpM $ \i -> if i < n then Nothing else Just $ var (i - n)

{-
lowerByN :: Subst a => Int -> Seq a -> a -> Maybe a
lowerByN 0 _ = pure
lowerByN n xs = mapExpM $ \i -> if i >= n then Just (var (i - n)) else IM.lookup i vars
  where
  vars = IM.fromList [ (v,var i) | (i, unVar -> Just v) <- zip [0..] (toList xs) ]
-}

--------------------------------------------------------------------------------
-- Substitution and friends for Bound
--------------------------------------------------------------------------------

substBound :: Subst a => Bound a -> a -> a
substBound x y = subst1 y (boundBody x)

-- Get the value from a bound where the name is not used
lowerBound :: Subst a => Bound a -> Maybe a
lowerBound = lowerBy 1 . boundBody

-- A 'Bound' where the bound name is not used
notBound :: Subst a => a -> Bound a
notBound = Bound "" . raiseBy 1

pattern NotBound x <- (Bound _ (lowerBy 1 -> Just x))

