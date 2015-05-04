{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
module TcMonad where

import Prelude ()
import Util.MyPrelude
import Util.PrettyM
import qualified Util.Tagged.Seq as TS
import qualified Util.Tagged.Map as TM
import Names
import Substitution
import Syntax

import qualified Data.Sequence as Seq
import qualified Data.Map as Map

--------------------------------------------------------------------------------
-- Typechecking/evaluation context
--------------------------------------------------------------------------------

-- types for all free variables
data TcCtx = TcCtx
  { ctxVarType  :: Seq (Named Exp) -- name and type of bound variables
  , ctxFreeType :: Map Name Exp -- types of free values
  --, ctxUsedNames  :: Set String    -- all names of bound variables
  }

emptyCtx :: TcCtx
emptyCtx = TcCtx
  { ctxVarType = Seq.empty
  , ctxFreeType = Map.empty
  }

pushCtx :: Named Exp -> TcCtx -> TcCtx
pushCtx typ ctx = ctx
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

metaUnresolved :: MetaValue -> Bool
metaUnresolved = isNothing . mvValue

--------------------------------------------------------------------------------
-- Monad
--------------------------------------------------------------------------------

newtype TcM a = TcM { unTcM :: ReaderT TcCtx (ExceptT Doc (State UnificationState)) a }
  deriving (Functor, Applicative, Monad, MonadError Doc)

instance MonadBound Exp TcM where
  localBound ty = TcM . local (pushCtx ty) . unTcM
  -- use the transformed type information in traverseBinder.
  traverseBinder f g h x y = g x >>= \x' -> f x' <$> traverseBound x' h y

instance MonadBoundNames TcM where
  boundNames = map namedName <$> boundTypes

instance MonadBoundTypes Exp TcM where
  boundTypes = TcM $ asks ctxVarType

runTcM :: TcCtx -> TcM a -> Either Doc a
runTcM ctx = flip evalState emptyUS . runExceptT . flip runReaderT ctx . unTcM

-- | Replace the context of bound variables
withCtx :: Seq (Named Exp) -> TcM a -> TcM a
withCtx bound = TcM . local (\ctx -> ctx{ctxVarType = bound}) . unTcM

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
freeType n = do
  mty <- TcM $ asks $ Map.lookup n . ctxFreeType
  case mty of
    Nothing -> throwError =<< text "Free variable has no type:" <+> text n
    Just ty -> return ty

--------------------------------------------------------------------------------
-- Error utilities
--------------------------------------------------------------------------------

tcError :: Doc -> TcM a
tcError err = throwError =<< pure err $$ dumpCtx $$ dumpMetas

dumpCtx :: TcM Doc
dumpCtx = text "With variables:" $$ indent 2 (vcat . toList . Seq.mapWithIndex pvar =<< boundTypes)
  where
  pvar i (Named n ty) = text n <.> text "#" <.> int i <+> text ":" <+> tcPpr 0 (raiseBy (i+1) ty)

dumpMetas :: TcM Doc
dumpMetas = do
  metas <- filter (metaUnresolved . snd) <$> getAllMetas
  case metas of
    [] -> emptyDoc
    ms -> text "With metas:" $$ indent 2 (vcat $ map (uncurry pprMeta) ms)

dumpAllMetas :: TcM Doc
dumpAllMetas =
  text "With metas:" $$ indent 2 (vcat . map (uncurry pprMeta) =<< getAllMetas) $$
  text "With level metas:" $$ indent 2 (vcat . map (uncurry pprLevelMeta) =<< getAllLevelMetas)

annError :: (Applicative m, MonadError Doc m) => m a -> m Doc -> m a
annError x y = catchError x $ \err -> do
  ann <- catchError y (const $ throwError err)
  throwError =<< pure err $$ pure ann

class EvalAllMetas a where
  evalAllMetas :: a -> TcM a
  evalAllMetasThrow :: a -> TcM a
  evalAllMetasWith :: (TcM Doc -> TcM ()) -> a -> TcM a
  evalAllMetas      = evalAllMetasWith (\_ -> return ())
  evalAllMetasThrow = evalAllMetasWith (\msg -> throwError =<< msg)

instance (EvalAllMetas a) => EvalAllMetas [a] where
  evalAllMetasWith f = traverse (evalAllMetasWith f)
instance (EvalAllMetas a, EvalAllMetas b) => EvalAllMetas (a,b) where
  evalAllMetasWith f = traversePair (evalAllMetasWith f) (evalAllMetasWith f)
instance EvalAllMetas Doc where
  evalAllMetasWith _ = pure
instance EvalAllMetas () where
  evalAllMetasWith _ = pure

tcPpr :: (EvalAllMetas a, Pretty TcM a) => Int -> a -> TcM Doc
tcPpr i x = ppr i =<< evalAllMetas x

pprMeta :: MetaVar -> MetaValue -> TcM Doc
pprMeta mv (MVExp val ty args) = ppr 0 mv <+> align (withCtx Seq.empty (go (toList $ Seq.reverse args)))
  where
  go [] = case val of
    Nothing -> text ":" <+> tcPpr 0 ty
    Just v  -> text ":" <+> tcPpr 0 ty <+> text "=" <+> ppr 0 v
  go (x:xs) = group $ ppr 11 x $$ localBound x (go xs)

pprLevelMeta :: LevelMetaVar -> Maybe Level -> TcM Doc
pprLevelMeta mv (Nothing) = ppr 0 mv <+> text ": Level"
pprLevelMeta mv (Just v) = ppr 0 mv <+> text "=" <+> ppr 0 v <+> text "=" <+> (ppr 0 =<< evalLevel v)

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

-- | Perform a function in the context of a metaValue
withMetaContext :: MetaVar -> TcM a -> TcM a
withMetaContext mv x = do
  args <- mvArgs <$> getMetaVar mv
  withCtx args x

--------------------------------------------------------------------------------
-- Expanding metas
--------------------------------------------------------------------------------

metaType :: MetaVar -> Seq Exp -> TcM Exp
metaType mv args = substsN args . mvType <$> getMetaVar mv

metaValue :: MetaVar -> Seq Exp -> TcM (Maybe Exp)
metaValue mv args = fmap (substsN args) . mvValue <$> getMetaVar mv

-- Evaluate metas at the top
evalMetas :: Exp -> TcM Exp
evalMetas x@(Meta mv args) = do
  x' <- metaValue mv args
  case x' of
    Nothing  -> pure x
    Just x'' -> evalMetas x''
evalMetas x = pure x

-- Evaluate all metas, give an error for unresolved ones
evalAllExpMetas :: (TcM Doc -> TcM ()) -> Exp -> TcM Exp
evalAllExpMetas err (Meta mv args) = do
  x' <- metaValue mv args
  case x' of
    Nothing  -> do err (text "Unresolved meta:" <+> tcPpr 0 (Meta mv args)
                        $$ text "of type" <+> (tcPpr 0 =<< metaType mv args))
                   Meta mv <$> traverse (evalAllExpMetas err) args
    Just x'' -> evalAllExpMetas err x''
evalAllExpMetas err (Set i) = Set <$> evalLevelWith err i
evalAllExpMetas err x = traverseChildren (evalAllExpMetas err) x

instance EvalAllMetas Exp where
  evalAllMetasWith = evalAllExpMetas

--------------------------------------------------------------------------------
-- Expand metas in levels
--------------------------------------------------------------------------------

evalLevel :: Level -> TcM Level
evalLevel = evalLevelWith (const $ return ())

evalLevelWith :: (TcM Doc -> TcM ()) -> Level -> TcM Level
evalLevelWith _ x@(IntLevel _) = pure x
evalLevelWith err (Level i j) = do
  lvl'@(Level _ j') <- foldr maxLevel (intLevel i) <$> mapM evalLevelVar (TM.toList j)
  unless (TM.null j') $ do
    err (traceM "unresolved level" >> text "Unresolved level metas in" <+> ppr 0 lvl')
  return lvl'

evalLevelVar :: (LevelMetaVar, Int) -> TcM Level
evalLevelVar (mv,add) = do
  l <- getLevelMetaVar mv
  case l of
    Nothing -> return $ addLevel add (metaLevel mv)
    Just l' -> addLevel add <$> evalLevel l'

instance EvalAllMetas Level where
  evalAllMetasWith = evalLevelWith

--------------------------------------------------------------------------------
-- Expand metas in ctors and cases
--------------------------------------------------------------------------------

instance EvalAllMetas SumCtor where
  evalAllMetasWith err (SumCtor n x) = SumCtor n <$> evalAllMetasWith err x

