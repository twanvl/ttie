{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Names where

import Prelude ()
import Util.MyPrelude
import Util.Pretty
import Util.Parser

import qualified Data.Map as Map
import qualified Data.Set as Set

--------------------------------------------------------------------------------
-- Helper type: names are strings
--------------------------------------------------------------------------------

type Name = String
type Names = Set Name

nameVariants :: Name -> [String]
nameVariants "" = ["x" ++ show i | i <- [1::Int ..]]
nameVariants name = [name,name++"'",name++"''"] ++ [name ++ show i | i <- [1::Int ..]]

-- A variant of the given name that does not appear in the set ns
freshNameVariants :: Names -> Name -> [Name]
freshNameVariants ns n = filter (`Set.notMember` ns) (nameVariants n)

freshNameVariant :: Names -> Name -> Name
freshNameVariant ns n = head $ freshNameVariants ns n

-- Some names are infix
infixNames :: [(Name,(Int,Int,Int))]
infixNames =
  [("_+_",(6,7,6)),("_*_",(7,8,7))
  ,("_++_",(5,6,5))
  ,("_==_",(4,5,5)),("_<_",(4,5,5)),("_>_",(4,5,5)),("_<=_",(4,5,5)),("_>=_",(4,5,5))]

--------------------------------------------------------------------------------
-- Helper type: binding names
--------------------------------------------------------------------------------

data Bound a = Bound
  { boundName :: Name
  --, boundFree :: Names -- names free in the body
  , boundBody :: a
  }
  deriving ()

instance Eq a => Eq (Bound a) where
  a == b = boundBody a == boundBody b

-- Note: Bound is not Traversible, to prevent mistakes wrt. keeping track of the bound values
traverseBound :: Functor f => (Int -> a -> f b) -> Int -> Bound a -> f (Bound b)
traverseBound f l (Bound n x) = Bound n <$> f (l+1) x

--------------------------------------------------------------------------------
-- Helper type: naming things
--------------------------------------------------------------------------------

data Named a = Named
  { namedName :: Name -- irrelevant for Eq
  --, namedUsed :: Bool -- is the bound name used? if not, it can be replaced by an arbitrary name
  , namedValue :: a
  }
  deriving (Functor, Foldable, Traversable)

named :: Name -> a -> Named a
--named "" = unnamed
named n  = Named n

unnamed :: a -> Named a
unnamed = Named ""

instance Eq a => Eq (Named a) where
  a == b = namedValue a == namedValue b

instance Show a => Show (Named a) where
  showsPrec p (Named n ty)
    | null n = showsPrec p ty
    | otherwise = showParen (p > 0) $ showString n . showString " : " . shows ty

--------------------------------------------------------------------------------
-- Helper type: hidden or visible
--------------------------------------------------------------------------------

data Hiding = Hidden | Visible
  deriving (Eq,Ord,Show)

data Arg a = Arg
  { argHiding :: Hiding
  , argValue  :: a
  }
  deriving (Eq, Functor, Foldable, Traversable)

visible, hidden :: a -> Arg a
visible = Arg Visible
hidden  = Arg Hidden

type NamedArg a = Arg (Named a)

namedArgName :: NamedArg a -> Name
namedArgName = namedName . argValue

namedArgValue :: NamedArg a -> a--
namedArgValue = namedValue . argValue

--------------------------------------------------------------------------------
-- Renaming for printing
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

namedBound :: Arg a -> Bound b -> (NamedArg a,b)
namedBound x y = (named (boundName y) <$> x, boundBody y)

instance Pretty a => Pretty (Named a) where
  ppr p (Named "" a) = ppr p a
  ppr p (Named n  a) = group $ parenIf (p > 0) $ ppr 1 n $/$ text ":" <+> ppr 0 a

instance Pretty a => Pretty (Bound a) where
  ppr p (Bound n a) = group $ parenIf (p > 0) $ brackets (ppr 0 n) <+> ppr 0 a

instance Pretty a => Pretty (Arg a) where
  ppr p (Arg Visible a) = ppr p a
  ppr _ (Arg Hidden  a) = braces $ ppr 0 a

--------------------------------------------------------------------------------
-- Parsing
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

