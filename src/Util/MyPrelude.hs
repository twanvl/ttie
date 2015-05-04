{-# LANGUAGE BangPatterns, GeneralizedNewtypeDeriving, FlexibleInstances, TypeSynonymInstances, RankNTypes #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-imports -fno-warn-orphans #-}

-- |
-- A more generic variant of the standard Prelude.
-- Uses Functor, Foldable, Traversable instead of List specific functions where appropriate.
-- Exports a lot of monad transformers.
-- And contains some generic utility functions
module Util.MyPrelude
  ( -- prelude stuff
    -- reexported, because I want to exclude list functions,
    -- instead use Foldable/Traversable
    Eq(..), Ord(..)
  , Show(..), ShowS, shows, showString, showParen
  , Num(..), Integral(..), fromIntegral, Real(..), Fractional(..), RealFrac(..), subtract
  , Enum(..)
  , Read(..), read
  , id, (.), ($), flip, const
  , fst, snd, curry, uncurry
  , first, second, (***)
  , seq
  , Int
  , Char, String, (++), null, length, (!!)
  , sort, sortBy
  , take, drop, takeWhile, dropWhile, reverse
  , zip, zipWith
  , iterate, head, tail, init, last, filter
  , Monad(..), join, when, unless, (=<<), (>=>), (<=<), ap, liftM, liftM2
  , zipWithM
  , MonadPlus(..), guard
  , error, undefined
  , MonadTrans(..)
  , module Data.Bool
  , module Data.Maybe
  , module Data.Either
  , module Data.Foldable
  , module Data.Traversable
  , module Data.Functor
  , module Control.Applicative
  , module Data.Monoid
  , module Data.Ord
  , module Data.Void
    -- io stuff
  , module System.IO
    -- more
  , module Util.MyPrelude
  , Seq, (|>), (<|)
  , Set
  , IM.IntMap
  , Map.Map
  , Identity(..)
  --, Constant(..) -- use Control.Applicative.Const
  , Compose(..)
  , MonadError(..), ExceptT(..), runExceptT, Except
  , ReaderT(..), MonadReader(..), Reader, runReader, asks
  , StateT(..), MonadState(..), State, evalState, execState, runState, evalStateT, execStateT, gets, modify
  , WriterT(..), MonadWriter(..), Writer, runWriter, execWriter, execWriterT
  , MonadFix(..)
  , module Control.Monad.Trans.Maybe
  , IdentityT(..)
  ) where

import Prelude hiding (map,mapM,concat,foldr,foldl,any)
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Data.Sequence (Seq,ViewL(..),ViewR(..),(<|),(|>))
import Data.Set (Set)
import Data.Graph (stronglyConnComp, SCC(..))
import Data.Foldable
import Data.Traversable
import Data.Functor
import Control.Monad hiding (mapM,mapM_)
import Control.Monad.Identity hiding (mapM,mapM_)
import Data.Functor.Constant
import Data.Functor.Compose
import Control.Monad.Reader hiding (mapM,mapM_)
import Control.Monad.State.Strict hiding (mapM,mapM_)
import Control.Monad.Except hiding (mapM,mapM_)
import Control.Monad.Writer hiding (mapM,mapM_)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Identity (IdentityT(..))
import Control.Applicative
import Control.Arrow (first,second,(***))
import Data.Monoid
import Data.Bool
import Data.Maybe
import Data.Either
import Data.Function
import Data.Ord
import Data.List (intersperse,sort,sortBy,group,groupBy)
import Data.Void

import System.IO

-- for debug code
import Debug.Trace
import Data.IORef
import System.IO.Unsafe
import Control.Exception

--------------------------------------------------------------------------------
-- Prelude style utilities
--------------------------------------------------------------------------------

map :: Functor f => (a -> b) -> f a -> f b
map = fmap

infixr 9 .:
(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) f g x y = f (g x y)

map2 :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
map2 = map . map

traverse2 :: (Traversable t, Applicative f, Applicative g) => (a -> f (g b)) -> t a -> f (g (t b))
traverse2 f = getCompose . traverse (Compose . f)

--snub :: Ord a => [a] -> [a]
--snub = map head . group . sort

nubOrd :: Ord a => [a] -> [a]
nubOrd = nubOrdWith id

nubOrdWith :: Ord b => (a -> b) -> [a] -> [a]
nubOrdWith f = go Set.empty
  where
  go _ [] = []
  go seen (x:xs)
    | f x `Set.member` seen = go seen xs
    | otherwise = x : go (Set.insert (f x) seen) xs

sortWith :: Ord b => (a -> b) -> [a] -> [a]
sortWith f = sortBy (comparing f)

findDuplicates :: Ord a => [a] -> [a]
findDuplicates = map head . filter (not . null . drop 1) . group . sort

trySubtract :: Int -> Int -> Maybe Int
trySubtract i j
  | i <= j = Just (j - i)
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Tuples
--------------------------------------------------------------------------------

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

snd3 :: (a,b,c) -> b
snd3 (_,b,_) = b

thd3 :: (a,b,c) -> c
thd3 (_,_,c) = c

traversePair :: Applicative f => (a -> f c) -> (b -> f d) -> (a,b) -> f (c,d)
traversePair f g (x,y) = (,) <$> f x <*> g y

--------------------------------------------------------------------------------
-- Monad utilities
--------------------------------------------------------------------------------

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = liftM concat (mapM f xs)

infixr 2 <&&>, &&>

local' :: (r -> r') -> ReaderT r' f a -> ReaderT r f a
local' f x = ReaderT $ \r -> runReaderT x (f r)

-- | Shortcutting version of @(&&)@
(&&>) :: Monad m => Bool -> m Bool -> m Bool
False &&> _ = return False
True  &&> x = x

-- | Shortcutting version of @(&&)@
(<&&>) :: Monad m => m Bool -> m Bool -> m Bool
mx <&&> my = mx >>= (&&> my)

-- | Shortcutting version of @and@
andM :: Monad m => [m Bool] -> m Bool
andM = foldr (<&&>) (return True)

--------------------------------------------------------------------------------
-- Show utilities
--------------------------------------------------------------------------------

catShows :: [ShowS] -> ShowS
catShows = foldr (.) id

showListWithSep :: String -> (a -> ShowS) -> [a] -> ShowS
showListWithSep sep sh = catShows . intersperse (showString sep) . map sh

--------------------------------------------------------------------------------
-- IntMap utilities
--------------------------------------------------------------------------------

-- | Return a key that is not in the given map.
freshKey :: IM.IntMap a -> Int
freshKey xs
  | IM.null xs = 0
  | otherwise = fst (IM.findMax xs) + 1

--------------------------------------------------------------------------------
-- Seq utilities
--------------------------------------------------------------------------------

pattern Empty <- (Seq.viewl -> Seq.EmptyL)
pattern x :< xs <- (Seq.viewl -> x Seq.:< xs)
pattern xs :> x <- (Seq.viewr -> xs Seq.:> x)

seqZipWithM :: Applicative m => (a -> b -> m c) -> Seq a -> Seq b -> m (Seq c)
seqZipWithM f a b = sequenceA (Seq.zipWith f a b)

seqZipWithM_ :: Applicative m => (a -> b -> m ()) -> Seq a -> Seq b -> m ()
seqZipWithM_ f a b = sequenceA_ (Seq.zipWith f a b)

seqCatMaybes :: Seq (Maybe a) -> Seq a
seqCatMaybes = foldl (\xs x -> maybe xs (xs |>) x) empty

seqLookup :: Int -> Seq a -> Maybe a
seqLookup i s
  | 0 <= i && i < Seq.length s = Just (Seq.index s i)
  | otherwise                  = Nothing

--------------------------------------------------------------------------------
-- Graph
--------------------------------------------------------------------------------

type Graph a = Map.Map a [a]

isAcyclic :: (Show a, Ord a) => Graph a -> Bool
isAcyclic = isNothing . findCycle

data Line a =Line a
instance Show a => Show (Line a) where show (Line x) = show x ++ "\n"

-- | Find a cycle if one exists
findCycle :: (Show a, Ord a) => Graph a -> Maybe [a]
findCycle g = listToMaybe
  [ c | CyclicSCC c <- stronglyConnComp g' ]
  where
  g' = [(x,x,ys) | (x,ys) <- Map.toList g]

graphSinks :: Graph a -> [a]
graphSinks g = [ x | (x,ys) <- Map.toList g, null ys ]

graphSources :: Ord a => Graph a -> [a]
graphSources = graphSinks . reverseGraph

reverseGraph :: Ord a => Graph a -> Graph a
reverseGraph g = Map.fromListWith (++) ([ (x,[]) | x <- Map.keys g ]
                                     ++ [ (y,[x]) | (x,ys) <- Map.toList g, y <- ys ])

--------------------------------------------------------------------------------
-- Debug utilities
--------------------------------------------------------------------------------

--debug :: Bool
--debug = False

-- use class to prevent CAF memoization
class IsBool a where
  fromBool :: Bool -> a
instance IsBool Bool where
  fromBool = id

debug :: IsBool a => a
debug = unsafePerformIO $ fromBool <$> readIORef debugVar
{-# INLINE debug #-}

debugVar :: IORef Bool
debugVar = unsafePerformIO $ newIORef True -- default debugging
{-# NOINLINE debugVar #-}

-- enable/disable trace messages at runtime (from GHCi)
enableDebug :: Bool -> IO ()
enableDebug = writeIORef debugVar

traceM :: Monad m => String -> m ()
traceM x = tracedM x $ return ()

traced :: String -> a -> a
traced msg x = unsafePerformIO $ tracedM msg (x `seq` evaluate x)

tracedM :: Monad m => String -> m a -> m a
tracedM msg x = do
  foo1 <- unsafePerformIO $ do
    lvl <- readIORef traceLevel
    when debug $ putStrLn (replicate (2*lvl) ' ' ++ msg)
    return $ return ()
  foo2 <- foo1 `seq` unsafePerformIO $ modifyIORef' traceLevel (+1) >> return (return ())
  a <- foo2 `seq` x
  foo3 <- foo2 `seq` unsafePerformIO $ modifyIORef' traceLevel (subtract 1) >> return (return ()) -- doesn't work with exceptions
  foo3 `seq` return a

traceBracket :: a -> a
traceBracket x = unsafePerformIO $
  bracket (readIORef traceLevel) (writeIORef traceLevel) (\_ -> evaluate x)

tracedM' :: Monad m => m String -> m a -> m a
tracedM' msg x = do
  m <- msg
  tracedM m x

{-# NOINLINE traceLevel #-}
traceLevel :: IORef Int
traceLevel = unsafePerformIO $ newIORef 0

traceLevel0 :: IO ()
traceLevel0 = writeIORef traceLevel 0

fromRight :: Show a => Either a b -> b
fromRight (Right x) = x
fromRight (Left x) = error $ "fromRight: Left " ++ show x

