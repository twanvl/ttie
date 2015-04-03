{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
module TcMonad where

import Prelude ()
import Util.MyPrelude
import Util.PrettyM
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
  , mvArgs  :: Seq (Named Exp) -- name and type of 'bound variables'
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

instance MonadBound Exp TcM where
  localBound ty = TcM . local (pushCtx ty) . unTcM

instance MonadBoundNames TcM where
  boundNames = map namedName <$> boundTypes

instance MonadBoundTypes Exp TcM where
  boundTypes = TcM $ asks ctxVarType

runTcM :: TcM a -> Either Doc a
runTcM = flip evalState emptyUS . runExceptT . flip runReaderT emptyCtx . unTcM

testTcM :: TcM a -> a
testTcM x = case runTcM x of
  Left e -> error (show e)
  Right y -> y

--------------------------------------------------------------------------------
-- Variables
--------------------------------------------------------------------------------

-- Name and type of bound variable
boundType :: Int -> TcM (Named Exp)
boundType i = do
  tys <- boundTypes
  if 0 <= i && i < Seq.length tys
    then return $ map (raiseBy (i+1)) $ Seq.index tys i
    else throwError =<< text "Variable not bound:" <+> int i

freeType :: Name -> TcM Exp
freeType n = throwError =<< text "Free variable has no type:" <+> text n

--------------------------------------------------------------------------------
-- Error utilities
--------------------------------------------------------------------------------

annError :: (Applicative m, MonadError Doc m) => m a -> m Doc -> m a
annError x y = catchError x $ \err -> do
  ann <- catchError y (const $ throwError err)
  throwError =<< pure err $$ pure ann

pprMeta :: MetaVar -> MetaValue -> TcM Doc
pprMeta mv (MVExp val ty args) = ppr 0 mv <+> tcWithoutCtx (go (toList $ Seq.reverse args))
  where
  tcWithoutCtx :: TcM a -> TcM a
  tcWithoutCtx = TcM . local (const emptyCtx) . unTcM
  go [] = case val of
    Nothing -> text ":" <+> ppr 0 ty
    Just v  -> text "=" <+> ppr 0 v
  go (x:xs) = ppr 11 x <+> localBound x (go xs)

pprLevelMeta :: LevelMetaVar -> Maybe Level -> TcM Doc
pprLevelMeta mv (Nothing) = ppr 0 mv <+> text ": Level"
pprLevelMeta mv (Just v) = ppr 0 mv <+> text "=" <+> ppr 0 v

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
  boundTys <- TcM $ asks $ ctxVarType
  mv <- freshMetaVar (MVExp Nothing ty boundTys)
  let args = Seq.fromList $ map Var [0..Seq.length boundTys-1]
  return (Meta mv args)

freshMetaLevel :: TcM Level
freshMetaLevel = metaLevel <$> freshLevelMetaVar

-- a fresh meta x : Set _
freshMetaSet :: TcM Exp
freshMetaSet = freshMeta . Set =<< freshMetaLevel

-- a fresh meta x : _ : Set _
freshMetaAny :: TcM Exp
freshMetaAny = freshMeta =<< freshMetaSet

getMetaVar :: MetaVar -> TcM MetaValue
getMetaVar mv = TcM $ gets $ TS.get mv . usMetas

modifyMetaVar :: MetaVar -> (MetaValue -> MetaValue) -> TcM ()
modifyMetaVar mv f = TcM $ modify $ modifyUsMetas $ TS.modify f mv

putMetaVar :: MetaVar -> MetaValue -> TcM ()
putMetaVar mv x = modifyMetaVar mv (const x)

getLevelMetaVar :: LevelMetaVar -> TcM (Maybe Level)
getLevelMetaVar mv = TcM $ gets $ TS.get mv . usLevelMetas

modifyLevelMetaVar :: LevelMetaVar -> (Maybe Level -> Maybe Level) -> TcM ()
modifyLevelMetaVar mv f = TcM $ modify $ modifyUsLevelMetas $ TS.modify f mv

putLevelMetaVar :: LevelMetaVar -> Maybe Level -> TcM ()
putLevelMetaVar mv x = modifyLevelMetaVar mv (const x)

getAllMetas :: TcM [(MetaVar,MetaValue)]
getAllMetas = TcM $ gets $ TS.toList . usMetas

getAllLevelMetas :: TcM [(LevelMetaVar,Maybe Level)]
getAllLevelMetas = TcM $ gets $ TS.toList . usLevelMetas

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

