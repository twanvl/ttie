{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module EqZipper where

import Prelude ()
import Data.List (inits)
import Util.MyPrelude
import Util.PrettyM
import Names
import Syntax
import Substitution

--------------------------------------------------------------------------------
-- Values of Eq types
--------------------------------------------------------------------------------

-- A value of an Eq type.
-- The integer indicates the number of times it is to be unwrapped.
-- The idea is that
--    WrappedExp 0 x == WrappedExp 1 (Refl x)
--    WrapepdExp 1 x == WrappedExp 0 (x^Var 0)
data WrappedExp = WrappedExp !Int Exp

wrappedExp :: Exp -> WrappedExp
wrappedExp = WrappedExp 0

weToUnwrap :: WrappedExp -> WrappedExp
weToUnwrap (WrappedExp 0 (Refl x)) = WrappedExp 0 (boundBody x)
weToUnwrap (WrappedExp i x) = WrappedExp (i+1) x

{-
weToWrap :: Name -> WrappedExp -> WrappedExp

weWrapped :: Name -> WrappedExp -> WrappedExp
weWrapped
-}

--------------------------------------------------------------------------------
-- Zipper for Eq values
--------------------------------------------------------------------------------

-- A path through Eq's
-- the type "Eq_i (Eq_j A a b) c d" is represented by path [EqStep j a b,EqStep i c d] and root type A
-- note: that the path specifies extra variables that are free in the type A
-- note2: the word 'path' refers to zipper terminology (a path up through the structure of the data type),
--        not path in the homotopy sense (an equality type)
--
-- notation:
--  Γ |- a : Set
--  -------------
--  Γ |- [] : path a
--
--  Γ |- ps : path (Eq_j a u v) 
--  --------------------
--  Γ |- (EqStep j u v:ps) : path a
type EqPath = [EqStep]
data EqStep = EqStep Name Exp Exp
  deriving (Show)

-- Names of the index variables
ezNames :: EqPath -> [Name]
ezNames = map (\(EqStep j _ _) -> j)

-- reverse the zipper.
-- notation:
--   Γ,ezNames p |- a : Set
--   ----------------------
--   Γ |- ezType a p : Set
ezType :: Exp -> EqPath -> Exp
ezType a0 ws = foldl step a0 ws
  where
  step a (EqStep j u v) = Eq (Bound j a) u v

-- Find the 'largest' path p, such that
-- (p,a) = ezFromType a0  ==>  a0 = ezType a p 
ezFromType :: Exp -> (Exp,EqPath)
ezFromType a0 = go a0 []
  where
  go (Eq (Bound j a) u v) path = go a (EqStep j u v:path)
  go a path = (a,path)

ezSubstPath :: Exp -> EqPath -> EqPath
ezSubstPath x ws = zipWith step ws [0..]
  where
  n = length ws
  step (EqStep j u v) i = EqStep j (substRaiseAt (n-1-i) x u) (substRaiseAt (n-1-i) x v)

ezRaisePathAtBy :: Int -> Int -> EqPath -> EqPath
ezRaisePathAtBy a b ws = zipWith step ws [0..]
  where
  n = length ws
  step (EqStep j u v) i = EqStep j (raiseAtBy (n-1-i+a) b u) (raiseAtBy (n-1-i+a) b v)

{-
ezSubstExp :: Exp -> EqPath -> Exp -> Exp
ezSubstExp x ws y = substAt (length ws) x y
-}

-- unwrap a boxed value into a larger context
--  Γ,ezNames p,Δ |- a : Set
--  Γ,Δ |- p : path a
--  Γ,Δ |- x : ezType a p
--  -------------------
--  Γ,ezNames p,Δ |- ezUnwrap |Δ| p x : a
ezUnwrap :: Int -> EqPath -> Exp -> Exp
ezUnwrap delta ws x0 = foldr step (raiseAtBy delta n x0) (zip ws [0..])
  where
  n = length ws
  step (_, i) (Refl x) = substBound x (Var (i+delta))
  step (EqStep _j u v, i) x = IV (raiseAtBy delta (i+1) u) (raiseAtBy delta (i+1) v) x (Var (i+delta))

-- wrap an expression in refls
--  Γ, ezNames p |- x : a
--  -------------------
--  Γ |- ezWrap p : ezType a p
ezWrap :: EqPath -> Exp -> Exp
ezWrap ws x0 = ezWrapNames (ezNames ws) x0

-- wrap an expression in refls
--  Γ,js |- x : a
--  -------------------
--  Γ |- ezWrapNames js : ezType a p,  where j = ezNames p
ezWrapNames :: [Name] -> Exp -> Exp
ezWrapNames js x0 = foldl step x0 js
  where
  step x j = Refl (Bound j x)

ezWrapNamesPath :: [Name] -> Exp -> EqPath
ezWrapNamesPath js0 x = zipWith3 step js0 (inits js0) [0..]
  where
  step j js i = EqStep j (ezWrapNames js (substAt i I0 x)) (ezWrapNames js (substAt i I1 x))

-- map inside refls
--  ∀ Δ. Δ |- x : a  ==>  Δ |- f x : b
--  Γ |- x : ezType a p
--  --------------------
--  Γ |- ezMapExp f p x : ezType b (ezMapPath f p)
ezMapExp :: (Exp -> Exp) -> EqPath -> Exp -> Exp
ezMapExp f ws x = ezWrap ws (f (ezUnwrap 0 ws x))

ezMapPath :: (Exp -> Exp) -> EqPath -> EqPath
ezMapPath f ws = zipWith step ws (inits ws)
  where
  step (EqStep j u v) inner = EqStep j (ezMapExp f (ezSubstPath I0 inner) u) (ezMapExp f (ezSubstPath I1 inner) v)

ezZipExp :: (Exp -> Exp -> Exp) -> EqPath -> Exp -> EqPath -> Exp -> Exp
ezZipExp f ws x ws' x' = ezWrap ws (f (ezUnwrap 0 ws x) (ezUnwrap 0 ws' x'))

ezZipPath :: (Exp -> Exp -> Exp) -> EqPath -> EqPath -> EqPath
ezZipPath f ws ws' = zipWith4 step ws (inits ws) ws' (inits ws')
  where
  step (EqStep j u v) inner (EqStep _j' u' v') inner' =
    EqStep j (ezZipExp f (ezSubstPath I0 inner) u (ezSubstPath I0 inner') u')
             (ezZipExp f (ezSubstPath I1 inner) v (ezSubstPath I1 inner') v')

--------------------------------------------------------------------------------
-- Values, used for casting
--------------------------------------------------------------------------------

-- A value of an Eq type
-- Note that the value has no extra free variables
-- On the other hand, the path has 1 extra free variable, namely the variable that is being cast along (Var 0)
--
-- Γ |- idx : Interval
-- Γ,i |- p : path a
-- Γ,i,p |- a : Set
-- Γ |- x : ezType a[i=idx] p[i=idx]
-- ---------------------------------
-- Γ |- castEqValue p x idx : CastEqValue a
data CastEqValue = CastEqValue
  { cevPath       :: EqPath
  , cevValue      :: Exp
  , cevCurrentIdx :: Exp -- ^ current 'side' of the variable that we are casting along (e.g. I0 when casting forward)
  }
  deriving (Show)

-- Γ |- cev : CastEqValue (Eq_j a u v)
-- -----------------------------------
-- Γ |- cevPush j u v cev : CastEqValue a
cevPush :: Name -> Exp -> Exp -> CastEqValue -> CastEqValue
cevPush j u v cev = cev { cevPath = EqStep j u v : cevPath cev }

cevDepth :: CastEqValue -> Int
cevDepth = length . cevPath

cevNames :: CastEqValue -> [Name]
cevNames = ezNames . cevPath

-- is the index used anywhere in the path?
cevIndexIsFree :: CastEqValue -> Bool
cevIndexIsFree cev = or $ zipWith step (cevPath cev) [0..]
  where
  n = cevDepth cev
  step (EqStep _ u v) i = isFree (n-1-i) u || isFree (n-1-i) v


-- Γ,i,js |- a : Type
-- Γ,js,Δ |- idx, idx' : Interval
-- Γ,js,Δ |- x : a[i=idx,js=js]
-- --------------------------
-- Γ,js,Δ |- cevConvertValue js |Δ| a idx idx' x : CastEqValue (raiseBy (n+delta) a)
cevConvertValue :: [Name] -> Int -> Exp -> Exp -> Exp -> Exp -> CastEqValue
cevConvertValue js delta a idx idx' x =
  cevSimpleValue js a'' idx idx' $ -- with Γ = Γ,js,Δ
  ezConvertValue js delta a' x -- Γ,js,Δ,js' : _ : a[i=idx,js=js']
  where
  n = length js
  a' = substAt (n+delta) idx $ raiseBy delta a -- Γ,js,Δ |- a' = a[i=idx]
  a'' = raiseAtBy (n+1) (n+delta) a --  Γ,js,Δ,i,js' |- a'' = a[i=idx,js=js']
  --idxD  = raiseBy (n+delta) idx  -- Γ,js,Δ |- idxD
  --idxD' = raiseBy (n+delta) idx' -- Γ,js,Δ |- idxD'

-- Γ,js,Δ |- a : Type
-- Γ,js,Δ |- x : a[js=js]
-- --------------------------
-- Γ,js,Δ,js' |- ezConvertValue js |Δ| a x : a[js=js']
ezConvertValue :: [Name] -> Int -> Exp -> Exp -> Exp
ezConvertValue js delta a x0 = foldl step (raiseBy n x0) (zip js [0..])
  where
  n = length js
  step x (j,i) = Cast (Bound j a') (Var (n+delta+i)) (Var i) x
    where
    a' = mapExp go a -- Γ,js,Δ,js',ji |- a'
    go k | k <  delta     = var (k+n+1) -- Δ
         | k <  delta + i = var (k-delta+1) -- ju with u<i
         | k == delta + i = var 0
         | otherwise      = var (k+n+1)

-- Γ |- idx, idx' : Interval
-- Γ,i,js |- a : Type
-- Γ,js   |- x : a[i=idx,js=js]
-- ----------------------------
-- Γ |- cevSimpleValue js a idx idx' x : CastEqValue a
cevSimpleValue :: [Name] -> Exp -> Exp -> Exp -> Exp -> CastEqValue
cevSimpleValue js a idx idx' x = CastEqValue
  { cevPath  = ezWrapNamesPath js xi
  , cevValue = ezWrapNames js x'
  , cevCurrentIdx = idx'
  }
  where
  n = length js
  ai = raiseToFront n a -- Γ,i',js,i |- ai
  a' = moveToFront n a  -- Γ,js,i |- a'
  -- Γ,i,js |- xi : a[i=i,js=js]
  xi = Cast (Bound "i" ai) (raiseBy (n+1) idx) (Var n) (raiseAtBy n 1 x)
  -- Γ,js |- x' : a[i=idx',js=js]
  x' = Cast (Bound "i" a') (raiseBy n idx) (raiseBy n idx') x

cevRaiseBy :: Int -> CastEqValue -> CastEqValue
cevRaiseBy delta cev = CastEqValue
  { cevPath  = ezRaisePathAtBy 1 delta (cevPath cev)
  , cevValue = raiseBy delta (cevValue cev)
  , cevCurrentIdx = raiseBy delta (cevCurrentIdx cev)
  }

cevRaiseTypeBy :: Int -> CastEqValue -> Exp -> Exp
cevRaiseTypeBy n cev = raiseAtBy (cevDepth cev + 1) n

-- Γ |- cev : CastEqValue a
-- ------------------------
-- Γ |- cevWrappedValue cev : cevType a cev
cevType :: Exp -> CastEqValue -> Exp
cevType a0 = ezType a0 . cevPath

--cevSubstBound :: Bound Exp -> CastEqValue -> CastEqValue
--cevSubstBound b cev = substBound b (cevUnwrappedValue cev)

cevCurrentPath :: CastEqValue -> EqPath
cevCurrentPath cev = ezSubstPath (cevCurrentIdx cev) (cevPath cev)

cevMap :: (Exp -> Exp) -> CastEqValue -> CastEqValue
cevMap f cev = CastEqValue
  { cevPath  = ezMapPath f (cevPath cev)
  , cevValue = ezMapExp f (cevCurrentPath cev) (cevValue cev)
  , cevCurrentIdx = cevCurrentIdx cev
  }

{-
ezMapValue :: (Exp -> Exp) -> EqValue -> EqValue
ezMapValue f (EqVal ws x) = EqVal (ezMapPath f ws) (ezMapExp f ws x)
-}

cevZipWith :: (Exp -> Exp -> Exp) -> CastEqValue -> CastEqValue -> CastEqValue
cevZipWith f x y = CastEqValue
  { cevPath  = ezZipPath f (cevPath x) (cevPath y)
  , cevValue = ezZipExp  f (cevCurrentPath x) (cevValue x) (cevCurrentPath y) (cevValue y)
  , cevCurrentIdx = cevCurrentIdx x -- current idx should be the same (not checked)
  }

cevWrappedValue :: CastEqValue -> Exp
cevWrappedValue = cevValue

-- Γ |- cev : CastEqValue a
-- ------------------------
-- Γ,cevNames cev,Δ |- cevUnwrappedValue cev : a
cevUnwrappedValue :: Int -> CastEqValue -> Exp
cevUnwrappedValue delta cev = ezUnwrap delta (cevCurrentPath cev) (cevValue cev)

--------------------------------------------------------------------------------
-- Debugging
--------------------------------------------------------------------------------

instance (MonadBound Exp m, MonadBoundNames m) => Pretty m EqPath where
  ppr _ xs0 = semiBrackets $ reverse (go (reverse xs0))
    where
    go :: (MonadBound Exp m, MonadBoundNames m) => EqPath -> [m Doc]
    go [] = []
    go (EqStep j u v:xs) =
      align (text "EqStep" <+> ppr 11 j $/$ ppr 11 u $/$ ppr 11 v) : map (localBound (Named j Interval)) (go xs)
instance (MonadBound Exp m, MonadBoundNames m) => Pretty m CastEqValue where
  ppr p cev = group $ parenAlignIf (p > 10) $ text "CastEqValue"
    $/$ localBound (Named "i" Interval) (ppr 11 (cevPath cev))
    $/$ ppr 11 (cevValue cev)
    $/$ ppr 11 (cevCurrentIdx cev)

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------
{-
-- zero layers
t0 :: Exp
t0 = pe "(x:A #1 #0)*(B #1 #0 x)"
t0p = snd $ ezFromType t0
t0c = ezZipValue (\a b -> Pair (visible a) b (fst $ ezFromType t0))
                 (ezMapValue (Proj (visible Proj1)) $ EqVal t0p (AppV (Free "foo") (Var 0)))
                 (ezMapValue (Proj (visible Proj2)) $ EqVal t0p (AppV (Free "foo") (Var 0)))

-- one layer
t1 :: Exp
t1 = pe "Eq_i ((x:A #0)*(B #0 x)) (u #0) (v #0)"
t1p = snd $ ezFromType t1
t1c = ezZipValue (\a b -> Pair (visible a) b (fst $ ezFromType t1))
                 (ezMapValue (Proj (visible Proj1)) $ EqVal t1p (AppV (Free "foo") (Var 0)))
                 (ezMapValue (Proj (visible Proj2)) $ EqVal t1p (AppV (Free "foo") (Var 0)))


-- two layers
t2e :: Exp
t2e = pe "Eq_i (Eq_j (A #0 i j) (a #0 i) (b #0 i)) (c #0) (d #0)"
t2p = snd $ ezFromType t2e
t2 = ezMapExp (Proj (visible Proj1)) t2p (AppV (Free "foo") (Var 0))
t2a = ezUnwrap t2p (AppV (Free "foo") (Var 0))
t2b = ezMapValue (Proj (visible Proj1)) $ EqVal t2p (AppV (Free "foo") (Var 0))
t2b' = ezMapValue (Proj (visible Proj2)) $ EqVal t2p (AppV (Free "foo") (Var 0))
t2q = ezMapPath (Proj (visible Proj1)) t2p
t2c = ezZipValue (\a b -> Pair (visible a) b (Free "AB" `AppV` Var 2 `AppV` Var 1 `AppV` Var 0)) t2b t2b'

-- three layers
t3 :: Exp
t3 = pe "Eq_i (Eq_j (Eq_k (A #0 i j) (a #0 i j) (b #0 i j)) (c #0 i) (d #0 i)) (e #0) (f #0)"
t3p = snd $ ezFromType t3
t3q = ezMapPath (Proj (visible Proj1)) t3p
-}

{-

evalCast s (Eq (Bound j a) x y) i1 i2 z =
  evalCast s a i1 i2 (consEqStep (EqStep j x y) z)
evalCast s (Si (Visible v a) b) i1 i2 z =
  let z1 = ezMap (Proj (Visible v Proj1)) z
      z2 = 
  let z1' = \i2' -> evalCast a i1 i2' z1
      z2' = ezCast b i1 i2 z2
  ezPair 
-}

{-

Cast (Eq (Bound j a) x y) p i1 i2 z =
  Cast a (EqStep j x y:p) i1 i2 z
Cast (A*B) p i1 i2 z =
  z1  = ezMapExp (Proj (Visible v Proj1)) (ezSubstPath i1 p) z
  z2  = ezMapExp (Proj (Visible v Proj2)) (ezSubstPath i1 p) z
  z1' = Cast a (ezMapPath proj1 p) i1 i2 z1
  z1R = Cast (ezRaiseType p a) (ezRaisePath p) (ezRaiseExp p i1) (Var 0) (ezRaiseExp p z1)
  z1R = Cast a (ezMapPath proj1 p) i1 i2 z1
  b'  = ezSubstType p z1R b
  z2' = Cast b' (ezMapPath proj2 p) i1 i2 z2
  z'  = ezZipExp (\u v -> Pair u v (Si a b'')) z1' z2'
  in z'
  
Cast (A->B) p i1 i2 z =
-}
{-
-- with HOAS

freeUp :: Exp -> (Exp -> Exp, (Exp -> Exp) -> Exp)

Cast i (A*B) p i1 i2 z =
  z1 = ezMapExp (Proj (Visible v Proj1)) (p i1) z
  


-}

{-

An Exp with n free variables, not necessarily (Var 0..Var (n-1))

data Nat = Zero | Suc Nat

data FExp n where
  ExpZ :: Exp    -> FExp Zero
  ExpS :: FExp n -> FExp


-}


{-


-}
