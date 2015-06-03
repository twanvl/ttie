{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
module Names where

import Prelude ()
import Util.MyPrelude
import Util.PrettyM
import Util.Parser

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Sequence as Seq

--------------------------------------------------------------------------------
-- Helper type: names are strings
--------------------------------------------------------------------------------

type Name = String
type Names = Set Name

nameVariants :: Name -> [String]
nameVariants "" = ["x" ++ show i | i <- [1::Int ..]]
nameVariants name = [name,name++"'",name++"''"] ++ [name ++ show i | i <- [1::Int ..]]

nameVariant :: Name -> String -> String
nameVariant "" x = "x" ++ x
nameVariant name x = name ++ x

-- A variant of the given name that does not appear in the set ns
freshNameVariants :: Names -> Name -> [Name]
freshNameVariants ns n = filter (`Set.notMember` ns) (nameVariants n)

freshNameVariant :: Names -> Name -> Name
freshNameVariant ns n = head $ freshNameVariants ns n

-- Some names are infix
infixNames :: [(Name,(Int,Int,Int))]
infixNames =
  [("_+_",(6,7,6)) --,("_*_",(7,8,7))
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

-- | Applicatives or monads that keep track of 
class Applicative f => MonadBound exp f where
  localBound :: Named exp -> f a -> f a

  traverseBound :: exp -> (a -> f b) -> Bound a -> f (Bound b)
  traverseBound ty f (Bound n x) = Bound n <$> localBound (named n ty) (f x)

  sequenceBound :: exp -> Bound (f a) -> f (Bound a)
  sequenceBound ty = traverseBound ty id

  -- traverse a binder, using the old exp for type information
  traverseBinder :: (exp -> Bound c -> d) -> (exp -> f exp) -> (a -> f c) -> exp -> Bound a -> f d
  traverseBinder = traverseBinderDefault

-- traverse a binder, using the old exp for type information
traverseBinderDefault :: MonadBound exp f => (b -> Bound c -> d) -> (exp -> f b) -> (a -> f c) -> exp -> Bound a -> f d
traverseBinderDefault f g h x y = f <$> g x <*> traverseBound x h y

class (Applicative f, Monad f) => MonadBoundNames f where
  boundNames :: f (Seq Name)
  boundNamesSet :: f (Set Name)
  boundNamesSet = Set.fromList . toList <$> boundNames
  boundDepth :: f Int
  boundDepth = Seq.length <$> boundNames

class (MonadBoundNames f, MonadBound exp f) => MonadBoundTypes exp f | f -> exp where
  boundTypes :: f (Seq (Named exp))

--------------------------------------------------------------------------------
-- Some instances of MonadBound
--------------------------------------------------------------------------------

instance Monoid a => MonadBound exp (Const a) where
  localBound _ = id
instance MonadBound exp Identity where
  localBound _ = id
instance MonadBound exp Maybe where
  localBound _ = id
instance MonadBound exp [] where
  localBound _ = id
instance (MonadBound exp f, Applicative g) => MonadBound exp (Compose f g) where
  localBound x (Compose y) = Compose (localBound x y)
instance (MonadBound exp f, Monad f) => MonadBound exp (MaybeT f) where
  localBound x (MaybeT y) = MaybeT (localBound x y)

newtype DepthT f a = DepthT { unDepthT :: ReaderT Int f a }
  deriving (Functor,Applicative,Monad)
instance Applicative f => MonadBound exp (DepthT f) where
  localBound _ = DepthT . local' succ . unDepthT
withDepth :: (Int -> f a) -> DepthT f a
withDepth = DepthT . ReaderT
runDepthT :: Int -> DepthT f a -> f a
runDepthT d0 = flip runReaderT d0 . unDepthT

newtype NamesT f a = NamesT { unNamesT :: ReaderT (Seq Name) f a }
  deriving (Functor,Applicative,Monad)
instance Applicative f => MonadBound exp (NamesT f) where
  localBound x = NamesT . local' (namedName x <|) . unNamesT
instance (Applicative f, Monad f) => MonadBoundNames (NamesT f) where
  boundNames = NamesT ask
runNamesT :: NamesT f a -> f a
runNamesT = flip runReaderT Seq.empty . unNamesT

--------------------------------------------------------------------------------
-- Traversing children of expressions
--------------------------------------------------------------------------------

class TraverseChildren exp a where
  traverseChildren :: MonadBound exp f => (exp -> f exp) -> (a -> f a)
  traverseChildren_ :: MonadBound exp f => (exp -> f ()) -> (a -> f ())
  traverseChildren_ f = fmap getConst . getCompose . traverseChildren (Compose . fmap Const . f)
  mapChildren :: (exp -> exp) -> (a -> a)
  mapChildren f = runIdentity . traverseChildren (Identity . f)

instance TraverseChildren exp a => TraverseChildren exp (Arg a) where
  traverseChildren f x = traverse (traverseChildren f) x

--------------------------------------------------------------------------------
-- Pretty Printing
--------------------------------------------------------------------------------

namedBound :: Arg a -> Bound b -> (NamedArg a,b)
namedBound x y = (named (boundName y) <$> x, boundBody y)

instance Pretty m a => Pretty m (Named a) where
  ppr p (Named "" a) = ppr p a
  ppr p (Named n  a) = group $ parenIf (p > 0) $ ppr 1 n $/$ text ":" <+> ppr 0 a

instance Pretty m a => Pretty m (Bound a) where
  ppr p (Bound n a) = group $ parenIf (p > 0) $ brackets (ppr 0 n) <+> ppr 0 a

instance Pretty m a => Pretty m (Arg a) where
  ppr p (Arg Visible a) = ppr p a
  ppr _ (Arg Hidden  a) = braces $ ppr 0 a

