{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TcMonad where

import Prelude ()
import Util.MyPrelude
import Util.Pretty
import qualified Util.Tagged.Seq as TS
import Names
import Substitution
import Syntax

import qualified Data.Sequence as Seq

--------------------------------------------------------------------------------
-- Typechecking/evaluation context
--------------------------------------------------------------------------------

-- types for all free variables
data Ctx = Ctx
  { ctxVarType :: Seq (Named Exp) -- name and type of bound variables
  --, ctxFreeValue  :: Map Name Decl -- 
  --, ctxUsedNames  :: Set String    -- all names of bound variables
  }

emptyCtx :: Ctx
emptyCtx = Ctx
  { ctxVarType = Seq.empty
  }

pushCtx :: Named Exp -> Ctx -> Ctx
pushCtx typ ctx = Ctx
  { ctxVarType   = typ <| ctxVarType ctx
  }

--------------------------------------------------------------------------------
-- Unification state
--------------------------------------------------------------------------------

data UnificationState = UnificationState
  { usMetas      :: TS.TaggedSeq "meta" MetaValue
  , usLevelMetas :: TS.TaggedSeq "level-meta" (Maybe Level)
  }

data MetaValue = MVExp
  { mvValue :: Maybe Exp
  , mvType  :: Exp
  }

emptyUS :: UnificationState
emptyUS = UnificationState
  { usMetas = TS.empty
  , usLevelMetas = TS.empty
  }

modifyUsMetas :: (TS.TaggedSeq "meta" MetaValue -> TS.TaggedSeq "meta" MetaValue)
               -> UnificationState -> UnificationState
modifyUsMetas f us = us { usMetas = f (usMetas us) }

modifyUsLevelMetas :: (TS.TaggedSeq "level-meta" (Maybe Level) -> TS.TaggedSeq "level-meta" (Maybe Level))
                   -> UnificationState -> UnificationState
modifyUsLevelMetas f us = us { usLevelMetas = f (usLevelMetas us) }

--------------------------------------------------------------------------------
-- Monad
--------------------------------------------------------------------------------

newtype TcM a = TcM { unTcM :: ReaderT Ctx (ExceptT Doc (State UnificationState)) a }
  deriving (Functor, Applicative, Monad, MonadError Doc)

tcLocal :: Named Exp -> TcM a -> TcM a
tcLocal ty = TcM . local (pushCtx ty) . unTcM

tcTraverse :: Exp -> (a -> TcM b) -> Bound a -> TcM (Bound b)
tcTraverse ty f (Bound n x) = Bound n <$> tcLocal (named n ty) (f x)

runTcM :: TcM a -> Either Doc a
runTcM = error "TODO"

--------------------------------------------------------------------------------
-- Getting/setting/adding MetaVars and LevelMetaVars
--------------------------------------------------------------------------------

freshMetaVar :: MetaValue -> TcM MetaVar
freshMetaVar value = TcM $ do
  (mv,usm') <- gets $ TS.insertNew value . usMetas
  modify $ modifyUsMetas $ const usm'
  return mv

freshLevelMetaVar :: TcM LevelMetaVar
freshLevelMetaVar = TcM $ do
  (mv,usm') <- gets $ TS.insertNew Nothing . usLevelMetas
  modify $ modifyUsLevelMetas $ const usm'
  return mv

freshMeta :: Exp -> TcM Exp
freshMeta ty = do
  mv <- freshMetaVar (MVExp Nothing ty)
  numBound <- TcM $ asks $ Seq.length . ctxVarType
  let args = Seq.fromList $ map Var [0..numBound-1]
  return (Meta mv args)

freshMetaSet :: TcM Exp
freshMetaSet = Set . metaLevel <$> freshLevelMetaVar

freshMetaAny :: TcM Exp
freshMetaAny = freshMeta =<< freshMetaSet

getMetaVar :: MetaVar -> TcM MetaValue
getMetaVar mv = TcM $ gets $ TS.get mv . usMetas

modifyMetaVar :: (MetaValue -> MetaValue) -> MetaVar -> TcM ()
modifyMetaVar f mv = TcM $ modify $ modifyUsMetas $ TS.modify f mv

putMetaVar :: MetaVar -> MetaValue -> TcM ()
putMetaVar mv x = modifyMetaVar (const x) mv

getLevelMetaVar :: LevelMetaVar -> TcM (Maybe Level)
getLevelMetaVar mv = TcM $ gets $ TS.get mv . usLevelMetas

modifyLevelMetaVar :: (Maybe Level -> Maybe Level) -> LevelMetaVar -> TcM ()
modifyLevelMetaVar f mv = TcM $ modify $ modifyUsLevelMetas $ TS.modify f mv

putLevelMetaVar :: LevelMetaVar -> Maybe Level -> TcM ()
putLevelMetaVar mv x = modifyLevelMetaVar (const x) mv

--------------------------------------------------------------------------------
-- Expanding metas
--------------------------------------------------------------------------------

metaType :: MetaVar -> Seq Exp -> TcM Exp
metaType mv args = substsN args . mvType <$> getMetaVar mv

metaValue :: MetaVar -> Seq Exp -> TcM (Maybe Exp)
metaValue mv args = fmap (substsN args) . mvValue <$> getMetaVar mv


{-
evalMeta :: Int -> Seq Exp -> Maybe Exp
evalMeta

evalLevelMetas :: Level -> TcM Level
evalLevelMetas (Level i j) = Level i 
-}

{-
unifyMetas :: Meta -> Meta -> 
unifyMeta
unifyMetas :: (Int,Seq Exp) -> (Int,Seq Exp)

unify :: Exp -> Exp -> TcM Exp
unify (App x y) (App x' y') = App <$> unify x x' <*> unify y y'

compareExp :: Exp -> Exp -> 

tryUnify :: Exp -> Exp -> TcM (Maybe Exp)

class MonadCompare where

unifySet :: Exp -> TcM LevelExp
unifyPi :: Hiding -> Exp -> TcM (Arg Exp, Bound Exp)
unifyPi (Pi x y) = return (x,y)
unifyPi xy = do
  x <- freshMetaAny
  y <- tcLocal (unnamed x) freshMetaAny
  unify (Pi x y) xy
  return (x,y)

Pi a b = Bound PiBinder a b
-}

