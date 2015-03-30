{-# LANGUAGE PolyKinds #-}
-- | Tagged integers
module Util.Tagged.Internal where

--------------------------------------------------------------------------------
-- Wrapped Int
--------------------------------------------------------------------------------

newtype TaggedVar tag = TV { tv :: Int }
  deriving (Eq)

instance Show (TaggedVar tag) where
  show = show . tv

