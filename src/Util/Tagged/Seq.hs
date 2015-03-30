{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveTraversable #-}
-- | Dense maps of tagged integers
module Util.Tagged.Seq where

import Util.MyPrelude
import Util.Tagged.Internal

import Data.Seq as Seq

--------------------------------------------------------------------------------
-- Wrapped Seq, used as a dense map
--------------------------------------------------------------------------------

newtype TaggedSeq tag a = TS { ts :: IntMap a }
  deriving (Functor,Foldable,Traversable,Eq)

empty :: TaggedSeq tag a
empty = TS IM.empty

null :: TaggedSeq tag a -> Bool
null = Seq.null . ts

-- insert a new variable at the end
insertNew :: a -> TaggedSeq tag a -> (TaggedVar tag, TaggedSeq tag a)
insertNew y (TS z) = (TV (Seq.size z), TS (z <| y))

get :: TaggedVar tag -> TaggedSeq tag a -> a
get (TV x) (TS y) = Seq.index x y

modify :: (a -> a) -> TaggedVar tag -> TaggedSeq tag a -> a
modify f (TV x) (TS y) = TS (Seq.adjust f x y)

toList :: TaggedSeq tag a -> [(TaggedVar tag, a)]
toList = zip (map TV [0..]) . Seq.toList . ts

