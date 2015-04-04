{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveTraversable #-}
-- | Maps of tagged integers
module Util.Tagged.Map where

import Util.MyPrelude
import Util.Tagged.Internal

import Data.IntMap as IM

--------------------------------------------------------------------------------
-- Wrapped IntMap
--------------------------------------------------------------------------------

newtype TaggedMap tag a = TM { tm :: IntMap a }
  deriving (Functor,Foldable,Traversable,Eq)

empty :: TaggedMap tag a
empty = TM IM.empty

null :: TaggedMap tag a -> Bool
null = IM.null . tm

singleton :: TaggedVar tag -> a -> TaggedMap tag a
singleton (TV x) y = TM (IM.singleton x y)

insert :: TaggedVar tag -> a -> TaggedMap tag a -> TaggedMap tag a
insert (TV x) y (TM z) = TM (IM.insert x y z)

unionWith :: (a -> a -> a) -> TaggedMap tag a -> TaggedMap tag a -> TaggedMap tag a
unionWith f (TM x) (TM y) = TM (IM.unionWith f x y)

toList :: TaggedMap tag a -> [(TaggedVar tag, a)]
toList = Prelude.map (first TV) . IM.toList . tm

mapMaybe :: (a -> Maybe b) -> TaggedMap tag a -> TaggedMap tag b
mapMaybe f = TM . IM.mapMaybe f . tm
