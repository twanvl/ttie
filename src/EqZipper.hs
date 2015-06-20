module EqZipper where

import Prelude ()
import Data.List (inits,zipWith4)
import Util.MyPrelude
import Names
import Syntax
import Substitution
import SubstitutionQQ

--------------------------------------------------------------------------------
-- Zipper for Eq values
--------------------------------------------------------------------------------

-- A path through Eq's
-- the type "Eq_i (Eq_j A a b) c d" is represented by path [EqStep j a b,EqStep i c d] and root type A
-- note that the path specifies extra variables that are free in the type A
type EqPath = [EqStep]
data EqStep = EqStep Name Exp Exp
  deriving (Show)

-- reverse the zipper
ezType :: Exp -> EqPath -> Exp
ezType a0 ws = foldl step a0 ws
  where
  step a (EqStep j u v) = Eq (Bound j a) u v

ezFromType :: Exp -> (Exp,EqPath)
ezFromType a0 = go a0 []
  where
  go (Eq (Bound j a) u v) path = go a (EqStep j u v:path)
  go a path = (a,path)

ezMapExp :: (Exp -> Exp) -> EqPath -> Exp -> Exp
ezMapExp f ws x = ezWrap ws (f (ezUnwrap ws x))

ezMapPath :: (Exp -> Exp) -> EqPath -> EqPath
ezMapPath f ws = zipWith step ws (inits ws)
  where
  step (EqStep j u v) inner = EqStep j (ezMapExp f (ezSubstPath I1 inner) u) (ezMapExp f (ezSubstPath I2 inner) v)

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

ezZipExp :: (Exp -> Exp -> Exp) -> EqPath -> Exp -> EqPath -> Exp -> Exp
ezZipExp f ws x ws' x' = ezWrap ws (f (ezUnwrap ws x) (ezUnwrap ws' x'))

ezZipPath :: (Exp -> Exp -> Exp) -> EqPath -> EqPath -> EqPath
ezZipPath f ws ws' = zipWith4 step ws (inits ws) ws' (inits ws')
  where
  step (EqStep j u v) inner (EqStep _j' u' v') inner' =
    EqStep j (ezZipExp f (ezSubstPath I1 inner) u (ezSubstPath I1 inner') u')
             (ezZipExp f (ezSubstPath I2 inner) v (ezSubstPath I2 inner') v')

{-
ezZipValue :: (Exp -> Exp -> Exp) -> EqValue -> EqValue -> EqValue
ezZipValue f (EqVal ws x) (EqVal ws' x') = EqVal (ezZipPath f ws ws') (ezZipExp f ws x ws' x')
-}

-- unwrap a boxed value into a larger context
ezUnwrap :: EqPath -> Exp -> Exp
ezUnwrap ws x0 = foldr step (raiseBy n x0) (zip ws [0..])
  where
  n = length ws
  step (EqStep _j u v, i) x = IV (raiseBy (i+1) u) (raiseBy (i+1) v) x (Var i)

ezWrap :: EqPath -> Exp -> Exp
ezWrap ws x0 = foldl step x0 ws
  where
  step x (EqStep j _ _) = Refl (Bound j x)

--------------------------------------------------------------------------------
-- Values, used for casting
--------------------------------------------------------------------------------

-- A value of an Eq type
-- Note that the value has no extra free variables
-- On the other hand, the path has 1 extra free variable, namely the variable that is being cast along (Var 0)
data CastEqValue = CastEqValue
  { cevPath       :: EqPath
  , cevValue      :: Exp
  , cevCurrentIdx :: Exp -- ^ current 'side' of the variable that we are casting along (e.g. I1 when casting forward)
  }
  deriving (Show)

cevPush :: Name -> Exp -> Exp -> CastEqValue -> CastEqValue
cevPush j u v cev = cev { cevPath = EqStep j u v : cevPath cev }

cevDepth :: CastEqValue -> Int
cevDepth = length . cevPath

-- is the index used anywhere in the path?
cevIndexIsFree :: CastEqValue -> Bool
cevIndexIsFree cev = or $ zipWith f (cevPath cev) [0..]
  where
  n = cevDepth cev
  f (EqStep _ u v) i = isFree (n-1-i) u || isFree (n-1-i) v

--cevFromValue :: Exp -> Exp -> 

--cevSourceType :: 

cevRaiseBy :: Int -> CastEqValue -> CastEqValue
cevRaiseBy n cev = CastEqValue
  { cevPath  = ezRaisePathAtBy 1 n (cevPath cev)
  , cevValue = raiseBy n (cevValue cev)
  , cevCurrentIdx = raiseBy n (cevCurrentIdx cev)
  }

cevRaiseTypeBy :: Int -> CastEqValue -> Exp -> Exp
cevRaiseTypeBy n cev = raiseAtBy (cevDepth cev + 1) n

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

cevZipWithValue :: (Exp -> Exp -> Exp) -> CastEqValue -> CastEqValue -> Exp
cevZipWithValue f x y = ezZipExp f (cevCurrentPath x) (cevValue x) (cevCurrentPath y) (cevValue y)

cevWrappedValue :: CastEqValue -> Exp
cevWrappedValue = cevValue

cevUnwrappedValue :: CastEqValue -> Exp
cevUnwrappedValue cev = ezUnwrap (cevCurrentPath cev) (cevValue cev)

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
