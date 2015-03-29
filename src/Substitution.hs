{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms #-}
module Substitution where

import Prelude ()
import Util.MyPrelude
import Util.Pretty
import Util.Parser

--import qualified Data.Map as Map
import qualified Data.IntMap as IM
import qualified Data.Sequence as Seq
--import Data.List (lookup,findIndex)
--import Data.Default.Class

--------------------------------------------------------------------------------
-- Substitution and friends
--------------------------------------------------------------------------------

class Subst a where
  var :: Int -> a
  unVar :: a -> Maybe Int
  mapExpM :: Applicative f => (Int -> f a) -> (a -> f a)

mapExp :: Subst a => (Int -> a) -> (a -> a)
mapExp f = runIdentity . mapExpM (pure . f)

raiseBy :: Subst a => Int -> a -> a
raiseBy i (unVar -> Just x) = var (i + x)
raiseBy 0 x = x
raiseBy n x = mapExp (\i -> var (n + i)) x

raiseSubsts :: Subst a => Int -> [a] -> (a -> a)
raiseSubsts n = mapExp . substsVar
  where
  substsVar []     i = var (n + i)
  substsVar (x:_)  0 = x
  substsVar (_:xs) i = substsVar xs (i - 1)

substs :: Subst a => [a] -> (a -> a)
substs = raiseSubsts 0

subst1 :: Subst a => a -> (a -> a)
subst1 x = substs [x]

substsN :: Subst a => Seq a -> (a -> a)
substsN Empty = id
substsN xs = mapExp $ \i -> if i < Seq.length xs
  then Seq.index xs i
  else var (i - Seq.length xs)

lowerBy :: Subst a => Int -> a -> Maybe a
lowerBy 0 = pure
lowerBy n = mapExpM $ \i -> if i < n then Nothing else Just $ var (i - n)

lowerByN :: Subst a => Int -> Seq a -> a -> Maybe a
lowerByN 0 _ = pure
lowerByN n xs = mapExpM $ \i -> if i >= n then Just (var (i - n)) else IM.lookup i vars
  where
  vars = IM.fromList [ (v,var i) | (i, unVar -> Just v) <- zip [0..] (toList xs) ]

-- does a variable occur free in the given expression
varUsed :: Subst a => Int -> a -> Bool
varUsed v = getAny . getConst . mapExpM (\i -> Const . Any $ i == v)

