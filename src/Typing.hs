{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DefaultSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE QuasiQuotes #-}
module Typing where

import Prelude ()
import Util.MyPrelude
import Util.PrettyM
import Syntax
import Substitution
import SubstitutionQQ
import Names
import TcMonad
import Eval

import qualified Data.Sequence as Seq
import qualified Data.IntMap as IM

--------------------------------------------------------------------------------
-- Transfering expressions between contexts
--------------------------------------------------------------------------------

-- | Transfer an expression to a different context, essentially the inverse of substitution.
-- This is a generalization of unsubstN.
-- Can unsubst metas ?1[a,b,c] when b can not be represented in the target
unsubst :: Seq Exp -> Exp -> TcM (Maybe Exp)
unsubst xs x0 = do
  l0 <- boundDepth
  if l0 /= Seq.length xs
    then error "Internal error: depth doesn't match number of arguments"
    else unsubst' l0 (invCtxMap xs) x0

unsubst' :: Int -> PartialCtxMap Exp -> Exp -> TcM (Maybe Exp)
unsubst' l0 vars x0 = go x0
  where
  go x = do
      l <- subtract l0 <$> boundDepth -- depth of the source
      x' <- evalMetas x
      case x' of
        Var i
          | i < l     -> return $ Just $ Var i
          | otherwise -> return $ raiseBy l <$> IM.lookup (i-l) vars
        Meta mv args -> do
          margs' <- mapM go args
          case sequence margs' of
            Just args' -> return $ Just $ Meta mv args'
            Nothing -> do
              -- we don't have to give up, we can replace ?1[#0,#1,#2,#3] by ?2[#0,#1] if e.g. #1 is not in vars
              -- i.e. keep only the Just arguments
              mval <- getMetaVar mv
              simpler <- filterCtx margs' (mvArgs mval) (mvType mval)
              case simpler of
                Nothing -> return Nothing
                Just (vars',args',tys',ty') -> do
                  -- make a new meta with only a subset of the context
                  mv' <- freshMetaVar (MVExp Nothing ty' tys')
                  -- let mv point to mv' (with a subset of the arguments)
                  modifyMetaVar mv $ \val -> val { mvValue = Just $ Meta mv' vars' }
                  {-
                  traceM $ "Unifying metas: " ++ show mv ++ " --> " ++ show mv'
                  traceM $ "Forwarded as " ++ show mv ++ " = " ++ show (Meta mv' vars')
                  traceM $ "Returned as " ++ show (Meta mv args) ++ " ~= " ++ show (Meta mv' args') ++ " by " ++ show vars
                  -}
                  return $ Just $ Meta mv' args'
        _ -> runMaybeT $ traverseChildren (MaybeT . go) x'

-- Suppose we are trying to abstract  (?2[#0,#1,#2] -> bar) to assign it to ?1[#0,foo #0,#3]
-- which means that we map #0->#0, #1->Nothing, #2->#3
-- and we encounter a meta  ?2[#0,#1,#2].
-- We have to replace this by a new meta ?3[#0,#2], and set ?2=?3[#0,#2], and ?1=?3[#0,#3]->bar
-- this is only allowed if this new made would be have well-typed arguments.

-- Make the type of a meta that takes just a subset of the arguments
filterCtx :: Seq (Maybe a) -- ^ arguments to keep (those for which we have a representation in the target context)
          -> Seq (Named Exp) -- ^ Original argument types
          -> Exp -- ^ original result type
          -> TcM (Maybe (Seq Exp, Seq a, Seq (Named Exp), Exp))
filterCtx xs0 tys0 ty0 = withCtx Seq.empty $ go Seq.empty xs0 tys0
  where
  -- vars gives for each variable in the context the corresponding index in tys
  go vars (xs :> Just x) (tys :> Named n ty) = do
    mty' <- unsubst vars ty
    case mty' of
      Nothing  -> go vars xs tys
      Just ty' -> do
        map (\(vars',xs',tys',ty0') -> (vars', xs' |> x, tys' |> Named n ty', ty0'))
          <$> localBound (Named n ty') (go (Var 0 <| map (raiseBy 1) vars) xs tys)
  go vars (xs :> Nothing) (tys :> _ty) = do
    go (map (raiseBy 1) vars) xs tys
  go vars _ _ = do
    map (\ty0' -> (vars,Seq.empty,Seq.empty,ty0'))
      <$> unsubst vars ty0

--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------

-- make sure actual/expected arguments stay in the right order
type Swapped = (forall a b. (a -> a -> b) -> (a -> a -> b))

-- | Verify that a meta doesn't occur in an expression
occursCheck :: MetaVar -> Exp -> TcM ()
occursCheck mv (Meta mv' _) | mv == mv' = throwError =<< text "Occurs check failed"
occursCheck mv x = traverseChildren_ (occursCheck mv) x

-- | Set a unification variable
-- Doesn't verify types
unifyMeta, unifyMeta' :: Swapped -> MetaVar -> Seq Exp -> Exp -> TcM Exp
unifyMeta swapped mv args y = do
  mx <- metaValue mv args
  case mx of
    Just x  -> swapped unify x y -- x already has a value, unify with that
    Nothing -> unifyMeta' swapped mv args =<< evalMetas y
unifyMeta' _ mv args (Meta mv' args') | mv' == mv =
  Meta mv <$> sequenceA (Seq.zipWith unify args args')
unifyMeta' swapped mv args (Meta mv' args') | Seq.length args < Seq.length args' =
  -- unify the other way around, otherwise unsubstN will fail
  unifyMeta' (flip . swapped) mv' args' (Meta mv args)
unifyMeta' _swapped mv args y = do
  -- perform occurs check: y must not contain mv
  occursCheck mv y
  -- unify the type of the metavar
  mv_type <- mvType <$> getMetaVar mv
  (_,y_type) <- tc Nothing y
  _ <- unify mv_type y_type
  -- y can only use variables that occur in args
  my' <- withMetaContext mv $ unsubst args y
  case my' of
    Nothing -> tcError =<< text "Variables not in scope of meta"
                           $$ indent 2 (tcPpr 0 (Meta mv args))
                           $$ indent 2 (tcPpr 0 y)
    Just y' -> do
      modifyMetaVar mv $ \val -> val { mvValue = Just y' }
      return y

-- | Rexpress x in terms of the local context
--(Int -> Maybe ) -> Exp -> TcM Exp

unifyLevelMeta :: Swapped -> LevelMetaVar -> Level -> TcM Level
unifyLevelMeta _swapped mv l = do
  lMv <- getLevelMetaVar mv
  if isJust lMv
    then error "unifyLevelMeta: meta var already has a value"
    else putLevelMetaVar mv (Just l)
  return l

unifyLevels, unifyLevels' :: Level -> Level -> TcM Level
unifyLevels x y = join $ unifyLevels' <$> evalLevel x <*> evalLevel y
unifyLevels' x y | x == y = pure x
unifyLevels' (MetaLevel x) y = unifyLevelMeta id   x y
unifyLevels' x (MetaLevel y) = unifyLevelMeta flip y x
unifyLevels' x y = do
  tcError =<< text "Failed to unify" <+> tcPpr 11 (Set x) <+> text "with" <+> tcPpr 11 (Set y)

-- | Unify two expressions.
-- requires that the expressions have the same type
-- does not assume that they are in normal form
unify :: Exp -> Exp -> TcM Exp
unify x y =
  unify' x y -- first try to unify without evaluation
  `catchError` \err -> do
    x' <- eval WHNF x
    y' <- eval WHNF y
    unless (isWHNF x') $ error $ "eval didn't produce WHNF: " ++ show x'
    unless (isWHNF y') $ error $ "eval didn't produce WHNF: " ++ show y'
    if x /= x' || y /= y'
      then unify' x' y' `catchError` \err' ->
           -- throw err', since in err we might have matched up wrong things
           throwError =<< pure err' $$ (text "When unifying" <+> tcPpr 11 x $/$ text "with" <+> tcPpr 11 y)
                                    $$ (text "Which simplifies to" <+> tcPpr 11 x' $/$ text "with" <+> tcPpr 11 y')
      else throwError =<< pure err  $$ (text "When unifying" <+> tcPpr 11 x $/$ text "with" <+> tcPpr 11 y)

-- | Unify two expressions that are in WHNF (or that we assume to have equal heads).
-- The left is the 'actual' type (of an argument e.g.),
-- the right is the 'expected' type (from a typesig, or applied function)
-- Optionally a value of the actual type may be passed in.
-- It will be applied to hidden arguments or wrapped in hidden lams/pairs as needed
unify' :: Exp -> Exp -> TcM Exp
--unify' x y | not (isWHNF x) || not (isWHNF y) = error $ "unify': arguments not in WHNF:" ++ show (x,y)
--unify' x y | not (isWHNF x) || not (isWHNF y) = tcError =<< text "unify': arguments not in WHNF:" <+> tcPpr 0 (x,y)
unify' (Set i) (Set i') = Set <$> unifyLevels i i'
unify' (Proj p x) (Proj p' x') | p == p' = Proj p <$> unify' x x'
unify' (App x (Arg h y)) (App x' (Arg h' y')) | h == h' = App <$> unify' x x' <*> (Arg h <$> unify' y y')
unify' (Binder b (Arg h x) y) (Binder b' (Arg h' x') y') | b == b' && h == h' = do
  x'' <- unify x x'
  Binder b (Arg h x'') <$> unifyBound x'' y y'
unify' (Pair (Arg h x) y z) (Pair (Arg h' x') y' z') | h == h' =
  Pair <$> (Arg h <$> unify x x') <*> unify y y' <*> unify z z'
unify' (SumTy xs) (SumTy xs') | length xs == length xs' = SumTy <$> zipWithM unifyCtor xs xs'
unify' (SumVal x y z) (SumVal x' y' z') | x == x' = SumVal x <$> unify y y' <*> unify z z'
unify' (SumElim x ys z) (SumElim x' ys' z') | length ys == length ys' = SumElim <$> unify x x' <*> zipWithM unifyCase ys ys' <*> unify z z'
unify' (IFlip x) (IFlip x') = IFlip <$> unify' x x'
unify' (Eq x y z) (Eq x' y' z') = Eq <$> unifyBound Interval x x' <*> unify y y' <*> unify z z'
unify' (Meta x args) y = unifyMeta id   x args y
unify' y (Meta x args) = unifyMeta flip x args y
unify' x y | x == y = return x
-- eta expansion and surjective pairing?
unify' (Pair (Arg h x) y z) x' =
  Pair <$> (Arg h <$> unify x (Proj (Arg h Proj1) x')) <*> unify y (Proj (Arg h Proj2) x') <*> pure z
unify' x (Pair (Arg h x') y' z') =
  Pair <$> (Arg h <$> unify (Proj (Arg h Proj1) x) x') <*> unify (Proj (Arg h Proj2) x) y' <*> pure z'
--unify' [qq| Lam (Arg h x) [$u](App y[] u)|] x' = 
unify' (Lam (Arg h x) y) f = Lam (Arg h x) <$> unifyBound x y (Bound "" (App (raiseBy 1 f) (Arg h (Var 0))))
unify' f (Lam (Arg h x) y) = Lam (Arg h x) <$> unifyBound x (Bound "" (App (raiseBy 1 f) (Arg h (Var 0)))) y
--unify' f (Lam (Arg h x) y) = Lam (Arg h x) <$> unifyBound x [qq| [$n] App f[] (Arg h n)|] y
unify' [qq|Refl [$_i](IV _ _ x[] _i)|] x' = unify x x'
unify' x [qq|Refl [$_i](IV _ _ x'[] _i)|] = unify x x'

unify' x y = do
  tcError =<< text "Failed to unify" <+> tcPpr 11 x <+> text "with" <+> tcPpr 11 y

unifyName :: Name -> Name -> Name
unifyName "" n = n
unifyName n _  = n

unifyBound :: Exp -> Bound Exp -> Bound Exp -> TcM (Bound Exp)
unifyBound ty (Bound n x) (Bound n' x') = Bound n'' <$> localBound (Named n'' ty) (unify x x')
  where n'' = unifyName n n'

unifyCtor :: SumCtor -> SumCtor -> TcM SumCtor
unifyCtor (SumCtor n x) (SumCtor n' x') | n == n' = SumCtor n <$> unify x x'
unifyCtor _ _ = tcError =<< text "Failed to unify constructors"

unifyCase :: SumCase -> SumCase -> TcM SumCase
unifyCase (SumCase n x y) (SumCase n' x' y') | n == n' = SumCase n <$> unify x x' <*> unifyBound x y y'
unifyCase _ _ = tcError =<< text "Failed to unify cases"


--unify' (Just valX) x (Pi (Arg Hidden u) v) =

-- | Unify x with (Set _)
unifySet :: Exp -> TcM Level
unifySet (Set i) = pure i
unifySet x = do
  i <- freshMetaLevel
  _ <- unify x (Set i)
  evalLevel i

-- | Unify x with (Binder b (Arg h _) _)
unifyBinder, unifyBinder' :: Binder -> Hiding -> Exp -> TcM (Exp, Bound Exp)
unifyBinder b h = unifyBinder' b h <=< eval WHNF
unifyBinder' b h (Binder b' (Arg h' x) y) | b == b' && h == h' = return (x,y)
unifyBinder' b h xy = do
  x <- freshMetaSet
  y <- Bound "" <$> localBound (unnamed x) freshMetaSet
  Binder _ (Arg _ x') y' <- unify xy (Binder b (Arg h x) y)
  return (x',y')

-- | Unify x with (Eq _ _ _)
unifyEq :: Exp -> TcM (Bound Exp, Exp, Exp)
unifyEq (Eq x y z) = return (x,y,z)
unifyEq xy = do
  x <- Bound "" <$> localBound (unnamed Interval) freshMetaSet
  y <- freshMeta (substBound x I1)
  z <- freshMeta (substBound x I2)
  Eq x' y' z' <- unify xy (Eq x y z)
  return (x',y',z')
  
-- | Unify x with (SumTy _)
unifySumTy :: Exp -> TcM [SumCtor]
unifySumTy (SumTy xs) = return xs
unifySumTy ty = tcError =<< text "Expected a sum type instead of" $/$ tcPpr 0 ty



-- To handle hidden arguments
--   unify (Pi Hidden x y) (Set _)
--   unify (Pi Hidden x y) (Pi Visible _ _)
--   unify (Si Hidden x y) _

-- Apply x of type ty to all expected hidden arguments if hiding=Visible
applyHidden :: Hiding -> Exp -> Exp -> TcM (Exp,Exp)
applyHidden Visible x ty = applyHidden' x =<< eval WHNF ty
applyHidden Hidden  x ty = return (x,ty)

applyHidden' :: Exp -> Exp -> TcM (Exp,Exp)
applyHidden' x (Pi (Arg Hidden u) v) = do
  arg <- freshMeta u
  let x'  = App x (hidden arg)
  let ty' = substBound v arg
  applyHidden' x' =<< eval WHNF ty'
applyHidden' x (Si (Arg Hidden _) v) = do
  let x'  = Proj (hidden Proj2) x
  let ty' = substBound v (Proj (hidden Proj1) x)
  applyHidden' x' =<< eval WHNF ty'
applyHidden' x ty = return (x,ty)

-- Ensure that x of type ty takes enough hidden arguments
{-
wrapHidden :: Hiding -> Exp -> Exp -> TcM (Exp,Exp)
wrapHidden Visible x ty = wrapHidden' x =<< eval WHNF ty
wrapHidden Hidden  x ty = return (x,ty)

wrapHidden' :: Exp -> Exp -> TcM (Exp,Exp)
wrapHidden' x (Pi (Arg Hidden u) v) = do
  Lam (Arg Hidden u)
  let x'  = App x (hidden arg)
  let ty' = substBound v arg
  (x' <- wrapHidden' x' =<< eval WHNF v
wrapHidden' x ty = pure (x,ty)
-}

--------------------------------------------------------------------------------
-- Typing
--------------------------------------------------------------------------------

-- Type checking and type inference
-- returns (expression, its type)
-- For typechecking, the argument must be well-typed, of type Set _
tc :: Maybe Exp -> Exp -> TcM (Exp,Exp)

tc Nothing (Var i) = do
  ty <- boundType i
  return (Var i, namedValue ty)
tc Nothing (Free x) = do
  ty <- freeType x
  return (Free x, ty)
tc Nothing (Proj p x) = do
  (x',x_ty) <- tc Nothing x
  (x'',x_ty') <- applyHidden (argHiding p) x' x_ty
  (ty1,ty2) <- unifyBinder SiB (argHiding p) x_ty'
  case argValue p of
    Proj1 -> return (Proj p x'', ty1)
    Proj2 -> return (Proj p x'', substBound ty2 (Proj (Proj1<$p) x''))
tc Nothing Blank = do
  ty <- freshMetaSet
  tc (Just ty) Blank
tc (Just ty) Blank = do
  x' <- freshMeta ty
  return (x',ty)
tc Nothing (Set i) = do
  i' <- evalLevel i
  return (Set i', Set (sucLevel i'))
tc Nothing (App x (Arg h y)) = do
  (x',x_ty) <- tc Nothing x
  (x'',x_ty') <- applyHidden h x' x_ty
  (ty1,ty2) <- unifyBinder PiB h x_ty'
  (y',_) <- tc (Just ty1) y
  return (App x'' (Arg h y'), substBound ty2 y')
tc Nothing (TypeSig x y) = do
  (y',_l) <- tcType y
  tc (Just y') x
tc (Just (Pi (Arg Hidden x) (Bound n y))) z@(Lam (Arg Visible _) _) = do
  -- wrap in \{_} -> ..
  (z',y') <- localBound (named n x) $ do
    y' <- eval WHNF y
    tc (Just y') (raiseBy 1 z)
  return (Lam (Arg Hidden x) (Bound n z'), Pi (Arg Hidden x) (Bound n y'))
tc (Just (Pi (Arg h x) (Bound n y))) (Lam (Arg h' x') (Bound n' z)) | h == h' = do
  -- propagate type information
  (x'',_) <- tcType x
  (x''',_) <- tcType x'
  xx <- unify x'' x'''
  let nn = unifyName n' n
  localBound (named nn xx) $ do
    (y',_) <- tcType y
    (z',_) <- tc (Just y') z
    return (Lam (Arg h xx) (Bound nn z'), Pi (Arg h xx) (Bound nn y'))
tc Nothing (Lam (Arg h x) (Bound n y)) = do
  (x',_) <- tcType x
  (y',t) <- localBound (named n x') (tc Nothing y)
  return (Lam (Arg h x') (Bound n y'), Pi (Arg h x') (Bound n t))
tc Nothing (Binder b (Arg h x) y) = do -- Pi or Sigma
  (x',lx) <- tcType x
  (y',ly) <- tcBoundType x' y
    `annError` text "in the second argument of a binder" $/$ tcPpr 0 (Binder b (Arg h x') y)
  return (Binder b (Arg h x') y', Set (maxLevel lx ly))
tc mty (Pair (Arg h x) y z) = do
  mty' <- tcMType mty z
  case mty' of
    Nothing -> do
      -- assume non-dependent pair
      (x',tx) <- tc Nothing x
      (y',ty) <- tc Nothing y
      let txy = Si (Arg h tx) (notBound ty)
      return (Pair (Arg h x') y' txy, txy)
    Just ty' -> do
      (ty1,ty2) <- unifyBinder SiB h ty'
      (x',_) <- tc (Just ty1) x
      (y',_) <- tc (Just $ substBound ty2 x') y
      return (Pair (Arg h x') y' ty', ty')
tc Nothing (Eq x y z) = do
  (x',l) <- tcBoundType Interval x
    `annError` text "in the 'type' argument of" $/$ tcPpr 0 (Eq x y z)
  (y',_) <- tc (Just $ substBound x' I1) y
    `annError` text "in the 'i1 end' argument of" $/$ tcPpr 0 (Eq x y z)
  (z',_) <- tc (Just $ substBound x' I2) z
    `annError` text "in the 'i2 end' argument of" $/$ tcPpr 0 (Eq x y z)
  return (Eq x' y' z', Set l)
tc Nothing (Refl (Bound n x)) = do
  (x',t) <- localBound (named n Interval) $ tc Nothing x
  return (Refl (Bound n x'), Eq (Bound n t) (subst1 I1 x') (subst1 I2 x'))
tc Nothing UnitTy = return (UnitTy, Set zeroLevel)
tc Nothing UnitVal = return (UnitVal, UnitTy)
tc Nothing (SumTy xs) = do
  let tcCtor (SumCtor n x) = do
        (x',l) <- tcType x
        return (SumCtor n x', l)
  xsls <- traverse tcCtor xs
  let xs' = sortWith ctorName $ map fst xsls
  let l = maxLevels $ map snd xsls
  case findDuplicates (map ctorName xs') of
    [] -> return ()
    ds -> tcError =<< text "Duplicate constructor names: " <+> hsep (map text ds)
  return (SumTy xs', Set l)
tc mty (SumVal n x y) = do
  my <- tcMType mty y
  case my of
    Nothing -> tcError =<< text "Type signature required for sum values"
    Just y' -> do
      ys <- unifySumTy y'
      cTy <- case find ((n==) . ctorName) ys of
        Nothing -> tcError =<< text "Constructor not in this type:" <+> text n <+> text "in" <+> tcPpr 0 y'
        Just (SumCtor _ cTy) -> return cTy
      (x',_) <- tc (Just cTy) x
      return (SumVal n x' y', y')
tc mty (SumElim x ys Blank) = do
  -- result type
  ty <- case mty of
    Nothing -> do
      -- assume non-dependent eliminator
      raiseBy 1 <$> freshMetaSet
    Just ty -> do
      -- ty is the type of the result, so with x instantiated.
      -- we can (try to) recover the pi type:
      -- if ty is of the form A[x], then the function type would be ((x:_) -> A[x])
      return $ unsubst1 x ty
  -- argument type
  (xTy,_) <- tc Nothing (SumTy (map caseToCtor ys))
  let z' = PiV xTy (Bound "" ty)
  tc Nothing (SumElim x ys z')
tc Nothing (SumElim x ys ty) = do
  (ty',_) <- tcType ty
  (ty1,ty2) <- unifyBinder PiB Visible ty'
  -- check argument
  (x',_) <- tc (Just ty1) x
  -- check cases
  ctors <- unifySumTy ty1
  let tcCase (SumCase n u (Bound m v)) = do
        -- unify type with type from signature
        u' <- case find ((==n) . ctorName) ctors of
          Nothing -> tcError =<< text "Constructor not found:" <+> text n
          Just c -> return (ctorType c)
        (u'',_) <- tcType u
        u''' <- unify u'' u'
        -- typecheck body
        let bodyTy = raiseSubsts 1 [SumVal n u''' ty1] (boundBody ty2)
        (v',_) <- localBound (named m u''') $ tc (Just bodyTy) v
        return (SumCase n u''' (Bound m v'))
  ys' <- traverse tcCase ys
  let ys'' = sortWith caseName ys'
  -- duplicate cases?
  case findDuplicates (map caseName ys'') of
    [] -> return ()
    ds -> tcError =<< text "Duplicate case names: " <+> hsep (map text ds)
  return (SumElim x' ys'' ty', substBound ty2 x')
tc Nothing Interval = return (Interval, Set zeroLevel)
tc Nothing I1  = return (I1, Interval)
tc Nothing I2  = return (I2, Interval)
tc Nothing I12 = return (I12, Eq (notBound Interval) I1 I2)
tc Nothing I21 = return (I21, Eq (notBound Interval) I2 I1)
tc Nothing (IFlip x) = do
  (x',_) <- tc (Just Interval) x
  return (IFlip x',Interval)
tc Nothing (IV x y z w) = do
  (w',_) <- tc (Just Interval) w
  (z',t) <- tc Nothing z
  (ta,t1,t2) <- unifyEq t
  (x',_) <- tc (Just $ substBound ta I1) x
  (y',_) <- tc (Just $ substBound ta I2) y
  _ <- unify x' t1
  _ <- unify y' t2
  return (IV x' y' z' w', substBound ta w')
tc Nothing (Cast x j1 j2 y) = do
  (x',_) <- tcBoundType Interval x
    `annError` text "in the 'type' argument of a cast"
  (j1',_) <- tc (Just Interval) j1
    `annError` text "in the 'source side' argument of a cast"
  (j2',_) <- tc (Just Interval) j2
    `annError` text "in the 'target side' argument of a cast"
  (y',_) <- tc (Just $ substBound x' j1') y
    `annError` text "in the 'value' argument of a cast"
  return (Cast x' j1' j2' y', substBound x' j2')
tc Nothing (Equiv a b c d e) = do
  l <- freshMetaLevel
  ty1 <- freshMeta (Set l)
  ty2 <- freshMeta (Set l)
  let x = "x"
  (a',_) <- tc (Just [qq| PiV ty1 [$x]ty2[] |]) a
  (b',_) <- tc (Just [qq| PiV ty2 [$x]ty1[] |]) b
  (c',_) <- tc (Just [qq| PiV ty1 [$x](Eq [$x]ty1[] (AppV b'[] (AppV a'[] x)) x) |]) c
  (d',_) <- tc (Just [qq| PiV ty2 [$x](Eq [$x]ty2[] (AppV a'[] (AppV b'[] x)) x) |]) d
  --(e',_) <- tc (Just [qq| PiV ty1 [$x]ty1[] |]) e
  let e' = e
  return (Equiv a' b' c' d' e', Eq (notBound (Set l)) ty1 ty2)
tc Nothing (Meta x args) = do
  val <- metaValue x args
  case val of
    Just x' -> tc Nothing x' -- eagerly get rid of known metas
    Nothing -> do
      ty <- metaType x args
      -- TODO: should I typecheck the args?
      return (Meta x args, ty)

tc (Just ty) x = do
  (x',tx) <- tc Nothing x
  ty'' <- unify ty tx
    `annError` (text "When checkinging that" <+> tcPpr 0 x' $/$ (text "has type" <+> tcPpr 0 ty))
  return (x',ty'')

-- check that x is a type, return its level
tcType :: Exp -> TcM (Exp, Level)
tcType x = do
  (x',l) <- tc Nothing x
  l' <- unifySet l
  return (x',l')

-- two possible sources of type signatures: inside the expression, and from the type argument to tc
tcMType :: Maybe Exp -> Exp -> TcM (Maybe Exp)
tcMType Nothing Blank = return Nothing
tcMType Nothing ty = Just . fst <$> tcType ty
tcMType (Just ty) Blank = return $ Just ty
tcMType (Just ty) ty' = do
  ty'' <- fst <$> tcType ty'
  Just <$> unify ty ty''

tcBoundType :: Exp -> Bound Exp -> TcM (Bound Exp, Level)
tcBoundType x (Bound n y) = do
  (y',l) <- localBound (named n x) $ tcType y
  return (Bound n y', l)

