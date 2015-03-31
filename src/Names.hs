{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
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
  deriving (Show)
-- Note: Bound is not Traversible, to prevent mistakes wrt. keeping track of the bound values
-- see TraverseBound class below

instance Eq a => Eq (Bound a) where
  a == b = boundBody a == boundBody b

{-
traverseBound :: Functor f => (Int -> a -> f b) -> Int -> Bound a -> f (Bound b)
traverseBound f l (Bound n x) = Bound n <$> f (l+1) x
-}

--------------------------------------------------------------------------------
-- Helper type: named things
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
-- Monads that can handle bound names
--------------------------------------------------------------------------------

-- An applied function
data Applied a b = (a -> b) :$ a

-- A monad that can be faked by using the input of an endo-function
-- this allows us to make Const an instance of MonadBound, by using the original value
class Applicative f => PseudoMonad f where
  (?>>=) :: Applied a (f a) -> (a -> f b) -> f b
  default (?>>=) :: Monad f => Applied a (f a) -> (a -> f b) -> f b
  (?>>=) (f :$ x) = (>>=) (f x)

-- | Applicatives or monads that keep track of 
class PseudoMonad f => MonadBound exp f where
  localBound :: Named exp -> f a -> f a

  traverseBound :: exp -> (a -> f b) -> Bound a -> f (Bound b)
  traverseBound ty f (Bound n x) = Bound n <$> localBound (named n ty) (f x)

  traverseBinder :: (exp -> Bound b -> c) -> (exp -> f exp) -> (a -> f b) -> exp -> Bound a -> f c
  traverseBinder f g h x y = (g :$ x) ?>>= \x' -> f x' <$> traverseBound x' h y

class Functor f => MonadBoundNames f where
  boundNames :: f (Seq Name)
  boundNamesSet :: f (Set Name)
  boundNamesSet = Set.fromList . toList <$> boundNames

class (MonadBoundNames f, MonadBound exp f) => MonadBoundTypes exp f where
  boundTypes :: f (Seq (Named exp))

--------------------------------------------------------------------------------
-- Some instances of MonadBound
--------------------------------------------------------------------------------

instance PseudoMonad Identity
instance PseudoMonad Maybe
instance PseudoMonad m => PseudoMonad (ReaderT r m) where
  (f :$ x) ?>>= y = ReaderT $ \r -> ((flip runReaderT r . f) :$ x) ?>>= (flip runReaderT r . y)
instance (Functor m, Monad m) => PseudoMonad (ExceptT e m) where

instance Monoid a => PseudoMonad (Const a) where
  (f :$ x) ?>>= g = f x *> g x
instance Monoid a => MonadBound exp (Const a) where
  localBound _ = id

newtype DepthT f a = DepthT { unDepthT :: ReaderT Int f a }
  deriving (Functor,Applicative,Monad,PseudoMonad)
instance PseudoMonad f => MonadBound exp (DepthT f) where
  localBound _ = DepthT . local' succ . unDepthT
withDepth :: (Int -> f a) -> DepthT f a
withDepth = DepthT . ReaderT
runDepthT :: Int -> DepthT f a -> f a
runDepthT d0 = flip runReaderT d0 . unDepthT

newtype NamesT f a = NamesT { unNamesT :: ReaderT (Seq Name) f a }
  deriving (Functor,Applicative,Monad,PseudoMonad)
instance PseudoMonad f => MonadBound exp (NamesT f) where
  localBound x = NamesT . local' (namedName x <|) . unNamesT

--------------------------------------------------------------------------------
-- Traversing children of expressions
--------------------------------------------------------------------------------

class TraverseChildren exp a where
  traverseChildren :: MonadBound exp f => (exp -> f exp) -> (a -> f a)

instance TraverseChildren exp a => TraverseChildren exp (Arg a) where
  traverseChildren f x = traverse (traverseChildren f) x

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

