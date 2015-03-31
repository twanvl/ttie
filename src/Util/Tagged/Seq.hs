{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveTraversable #-}
-- | Dense maps of tagged integers
module Util.Tagged.Seq where

import Prelude ()
import Util.MyPrelude as P
import Util.Tagged.Internal

import qualified Data.Sequence as Seq

--------------------------------------------------------------------------------
-- Wrapped Seq, used as a dense map
--------------------------------------------------------------------------------

newtype TaggedSeq tag a = TS { ts :: Seq a }
  deriving (Functor,Foldable,Traversable,Eq)

empty :: TaggedSeq tag a
empty = TS Seq.empty

null :: TaggedSeq tag a -> Bool
null = Seq.null . ts

-- insert a new variable at the end
insertNew :: a -> TaggedSeq tag a -> (TaggedVar tag, TaggedSeq tag a)
insertNew y (TS z) = (TV (Seq.length z), TS (z |> y))

get :: TaggedVar tag -> TaggedSeq tag a -> a
get (TV x) (TS y) = Seq.index y x

modify :: (a -> a) -> TaggedVar tag -> TaggedSeq tag a -> TaggedSeq tag a
modify f (TV x) (TS y) = TS (Seq.adjust f x y)

toList :: TaggedSeq tag a -> [(TaggedVar tag, a)]
toList = zip (map TV [0..]) . P.toList . ts

