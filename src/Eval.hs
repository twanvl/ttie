{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuasiQuotes, ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
module Eval where

import Prelude ()
import Data.List (lookup)
import Util.MyPrelude
import Util.Pretty
import Syntax
import Substitution
import SubstitutionQQ
import Names
import TcMonad

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

data EvalStrategy = WHNF | NF | MetaOnly | OneStep
  deriving (Eq)

data EvalEnv = EvalEnv
  { evalStrategy  :: EvalStrategy
  , evalMetaValue :: MetaVar -> Seq Exp -> Maybe Exp
  --, evalGlobal :: Name -> Seq Exp -> Maybe Exp
  --, evalGlobals
  }

eval :: EvalEnv -> Exp -> Exp
eval (evalStrategy->WHNF) x@(Pair _ _ _) = x
eval (evalStrategy->WHNF) x@(Binder _ _ _) = x
eval e (Meta x xs) = evalMeta e x xs
eval (evalStrategy->MetaOnly) x = x
eval e (TypeSig x _ty) = evalMore e x
eval e x = evalHere e $ mapChildren (evalMore e) x

evalHere :: EvalEnv -> Exp -> Exp
evalHere e (TypeSig x _ty)  = evalMore  e x
evalHere e (App x y)        = evalApp   e x y
evalHere e (Proj x y)       = evalProj  e x y
evalHere e (SumElim x ys z) = evalCase  e x ys z
evalHere e (IFlip x)        = evalIFlip e x
evalHere e (IV x y z w)     = evalIV    e x y z w
evalHere e (Eq x y z)       = evalEq    e x y z
evalHere e (Cast x y z w)   = evalCast  e x y z w
evalHere (evalStrategy->NF) x = etaContract x
evalHere _ x = x

evalMore :: EvalEnv -> Exp -> Exp
evalMore (evalStrategy->OneStep) x = x
evalMore e x = eval e x

evalMeta :: EvalEnv -> MetaVar -> Seq Exp -> Exp
evalMeta e x xs =
  case evalMetaValue e x xs of
    Nothing -> Meta x (map (eval e) xs)
    Just m' -> eval e m'

evalApp :: EvalEnv -> Exp -> Arg Exp -> Exp
evalApp e (Lam _ x) y = evalMore e $ substBound x (argValue y)
--evalApp s (Refl x `AppH` y `AppH` z) (Arg h w) = Refl (App x (Arg h (IV)))
--evalApp s [qq| Refl [$n]x `AppH` y `AppH` z|] (Arg h w) =
--  evalMore s $ [qq| Refl [$n](App x (Arg $h (IV y[] z[] w[] n))) |]
evalApp _ x y = App x y

evalProj :: EvalEnv -> Arg Proj -> Exp -> Exp
evalProj e (Arg _ Proj1) (Pair x _y _) = evalMore e (argValue x)
evalProj e (Arg _ Proj2) (Pair _x y _) = evalMore e y
--evalProj s p (Refl x) = Refl <$> traverseBound Interval (evalProj s p) x
evalProj _ p x = Proj p x

evalCase :: EvalEnv -> Exp -> [SumCase] -> Exp -> Exp
evalCase e (SumVal n x _) ys _
  | Just (SumCase _ _ y) <- find ((n==) . caseName) ys
  = evalMore e $ substBound y x
evalCase _ x ys a = SumElim x ys a

evalIFlip :: EvalEnv -> Exp -> Exp
evalIFlip _ I1 = I2
evalIFlip _ I2 = I1
evalIFlip _ (IFlip x) = x
evalIFlip _ x  = IFlip x

evalIV :: EvalEnv -> Exp -> Exp -> Exp -> Exp -> Exp
evalIV _ x _ _ I1 = x
evalIV _ _ y _ I2 = y
evalIV _ _ _ I12 w = w
evalIV e _ _ (Refl z) w = evalMore e $ substBound z w
evalIV _ x y z w  = IV x y z w

evalEq :: EvalEnv -> Bound Exp -> Exp -> Exp -> Exp
evalEq _ x y z = Eq x y z

--evalFw s [qq|Refl [$_n]x[] |] y = y
evalCast :: EvalEnv -> Bound Exp -> Exp -> Exp -> Exp -> Exp
--evalCast _ _ I1 I1 y = y
--evalCast _ _ I2 I2 y = y
evalCast _ _ j1 j2 y | j1 == j2 = y
evalCast _ (NotBound _) _ _ y = y
--
evalCast e [qq|[$i](Pi (Arg $h a) [$x]b)|] j1 j2 y = evalMore e
  [qq| Lam (Arg $h a[i=j2[]]) [$x]
       (Cast ([$i]b[i,x=Cast ([$i]a[i]) j2[] i x]) j1[] j2[]
             (App y[] (Arg $h (Cast ([$i]a[i]) j2[] j1[] x)))) |]
--
evalCast e [qq|[$i](Si (Arg $h a) [$x]b)|] j1 j2 y = evalMore e
  [qq| Pair (Arg $h (Cast [$i]a j1[] j2[] (Proj (Arg $h Proj1) y)))
                    (Cast [$i]b[i,x=Cast [$i]a[i] j1[] i (Proj (Arg $h Proj1) y[])]
                          j1[] j2[] (Proj (Arg $h Proj2) y))
            (Si (Arg $h a[i=j2[]]) [$x]b[i=j2[],x]) |]
--
evalCast e [qq|[$i](SumTy xs)|] j1 j2 (SumVal n y _)
  | Just ty <- traverse (map ctorType . find ((==n) . ctorName)) xs
  = evalMore e [qq|SumVal n (Cast [$i]ty j1 j2 y) tyxs[i=j2]|]
  where tyxs = SumTy <$> xs
--evalCast s [qq|(Bound i (Eq a x y))|] [qq|Refl (Bound _ z)|] = evalFwRefl i a x y z
evalCast e [qq|[$i](Eq [$_j]_a[_j] _x[] y)|] I1 I2 [qq|Refl (NotBound _)|] = evalMore e
  [qq| Refl [$i]y[i] |]
--
{-
evalCast s [qq|[$i](Eq [$j](Pi (Arg $h a) [$x]b) u v)|] i1 i2 y = evalMore s
  [qq| Refl [$j](Lam (Arg $h a[i=$i2,j])
            [$x](IV () () (Cast [$i]eqij[i,j1=j] i1[] i2[] ) j) )|]
  where
  xj2 = [qq|[~j1][~j2][~x]Cast ([$j]a[i2[],j]) j1 j2 x|] -- : A i2 j2
  xij = [qq|[~i][~j1][~j2][~x]Cast ([$i]a[i,j=j2]) i2[] i xj[j1,j2,x]|]
  xj1 = [qq|[~i][~j1][~j2][~x]IV (xij[i,j1,j2=I1,x])
                                 (xij[i,j1,j2=I2,x])
                                 (Cast ([$i]Eq ([$j]a[i,j]) xij[i,j1,j2=I1,x] xij[i,j1,j2=I2,x]) i2[] i
                                       (Refl [$j]xj2[j1,j2=j,x]))
                                 j2|] -- : A i j2
  bij = [qq|[~i][~j1][~j2][~x]
  eqj = [qq|[~i][~j1][~x] Eq ([$j]b[i,j,x=xj1[i,j1,x]])
  --
  xu = [qq|[~x]IV u
  x2 = [qq|[~x]Cast ([$i](Eq [$j]a[i,j] () ()) $i2 $i1 x |]-}
--
evalCast e [qq|[$i](Eq [$j](Si (Arg $h a) [$x]b) u v)|] i1 i2 y = evalMore e
  [qq| Refl [$j](Pair (Arg $h w1[i2=i2[],j])
                              w2[i2=i2[],j]
                      (Si (Arg $h a[i=i2[],j=j]) [$x]b[i=i2[],j=j,x])) |]
  where
  yk = [qq|[~j](IV u[i=i1[]] v[i=i1[]] y[] j)|] :: Wrap "j" Exp
  y1 = [qq|Refl [$j](Proj (Arg $h Proj1) yk)|]
  y2 = [qq|Refl [$j](Proj (Arg $h Proj2) yk)|]
  z1 = [qq|[~i2]Cast [$i](Eq [$j]a[i,j]              u1[i] v1[i]) i1[] i2 y1[]|]
  z2 = [qq|[~i2]Cast [$i](Eq [$j]b[i,j,x=w1[i2=i,j]] u2[i] v2[i]) i1[] i2 y2[]|]
  w1 = [qq|[~i2][~j] (IV u1[i=i2] v1[i=i2] z1[i2=i2] j)|]
  w2 = [qq|[~i2][~j] (IV u2[i=i2] v2[i=i2] z2[i2=i2] j)|]
  u1 = [qq|[~i]Proj (Arg $h Proj1) u|] :: Wrap "i" Exp
  u2 = [qq|[~i]Proj (Arg $h Proj2) u|]
  v1 = [qq|[~i]Proj (Arg $h Proj1) v|]
  v2 = [qq|[~i]Proj (Arg $h Proj2) v|]
--
--evalCast s [qq|[$i]a|] I2 j2 x = evalMore s [qq| Cast [$i]a[i=IFlip i] I1 (IFlip j2) x |]
--
evalCast _ a j1 j2 x = Cast a j1 j2 x

--evalCastEq ::
--evalCastEq s a x y z j1 j2 = pure [qq|Cast $j1 $j2 z|]

{-
fw_i (Eq_j A_12^i u v) w
fw_i (Eq_j A_12^j u v) w
fw_i (Eq (Eq x y) u v) w
fw_i (Eq (Eq x y) (refl u) (refl v)) (refl w)
-}

etaContract :: Exp -> Exp
etaContract (Pair (Arg h1 (Proj (Arg h2 Proj1) x)) (Proj (Arg h3 Proj2) y) _) | x == y && h1 == h2 && h1 == h3 = x
etaContract [qq|Lam (Arg h _) [$_x](App f[] (Arg $h' _x))|] | h == h' = f
etaContract [qq|Refl [$_i](IV _ _ x[] _i)|] = x
etaContract x = x

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Casting
--------------------------------------------------------------------------------
{-
-- x : A                      -->  Box x []
-- x : Eq_j A a b             -->  Box x [(j,a,b)]
-- x : Eq_j (Eq_k A c d) a b  -->  Box x [(j,a,b),(k,c,d)]
-- free variables:
--   x[], a[0=i], c[0=j,1=i]
--   where i is the variable being cast along.
-- types:
--   G |- x : (boxType A [(j,a,b),(k,c,d)])[i=1] (see above)
--   G,i |- a : (boxType A [(k,c,d)])[j=1]
--   G,i,j |- c : A[k=1]
--   G,i,j,k |- A : Type
data Box = Box
  { boxValue :: Exp
  , boxArgs  :: [(Name,Exp,Exp)]
  --, boxArgAt :: Exp
  }

noBox :: Exp -> Box
noBox x = Box x []

mapBox :: (Exp -> Exp) -> (Box -> Box)
mapBox f (Box x args) = undefined

-- type of the thing in the box (generalized with var 0 the variable that is cast along)
boxType :: Exp -> BoxArgs -> Exp
--boxType = foldr (\(j,u,v) t -> Eq (Bound j t) u v)
boxType a [] = a
boxType a ((j,u,v):ws) = Eq (Bound j (boxType a ws)) u v

-- map a simple function (without free vars) over the thing in a box
boxMap :: (Exp -> Exp) -> BoxArgs -> Exp -> Exp
boxMap f ws x = boxWrap ws (f (boxUnwrap ws x))

boxArgsMap :: (Exp -> Exp) -> BoxArgs -> BoxArgs
boxArgsMap f [] = []
boxArgsMap f 

-- unwrap a boxed value into a larger context
boxUnwrap :: BoxArgs -> Exp -> Exp
boxUnwrap [] x = x
boxUnwrap ((_j,u,v):ws) x = IV u v (raiseBy 1 (boxUnwrap ws x)) (Var 0)

boxWrap :: BoxArgs -> Exp -> Exp
boxWrap [] x = x
boxWrap ((j,_,_):ws) x = Refl (Bound j (boxWrap ws x))

-- substitute Var 0 in BoxArgs. This is the variable along which we are casting
boxArgsSubst :: Exp -> BoxArgs -> BoxArgs
boxArgsSubst = go 1
  where
  go n [] = []
  go n ((j,u,v):ws) = (j, substAt n (raiseBy n x) u, substAt n (raiseBy n x) v)
                    : go (n+1) x ws
-}
--------------------------------------

{-
-- A zipper to look inside Eq
data EqZipper a = EqRoot Exp | EqStep Exp Exp EqZipper

eqzRoot :: EqZipper a -> a
eqzRoot (EqRoot x) = x
eqzRoot (EqStep _ _ x) = eqzRoot x

eqzType :: EqZipper a -> Exp -> Exp

eqzToExp :: EqZipper -> Exp
eqzToExp (EqRoot x) = x
eqzToExp (EqStep u v x) = eqzToExp x

eqzMap :: 
-}

--traverseBox :: Box -> Box
{-
lamBox :: (Box -> Box) -> Box
-}

--------------------------------------------------------------------------------
-- Is an expression in WHNF?
--------------------------------------------------------------------------------

isWHNF :: Exp -> Bool
isWHNF (TypeSig _ _) = False
isWHNF (App (Lam _ _) _) = False
isWHNF (App x _) = isWHNF x
isWHNF (Proj _ (Pair _ _ _)) = False
isWHNF (Proj _ x) = isWHNF x
isWHNF (IV _ _ _ I1) = False
isWHNF (IV _ _ _ I2) = False
isWHNF (IV _ _ _ i) = isWHNF i
isWHNF _ = True

--------------------------------------------------------------------------------
-- Evaluation in all possible locations
--------------------------------------------------------------------------------

-- | Apply a function to x and all its children (independently), collect results
everywhereM :: (MonadBound Exp f, Alternative g) => (Exp -> f (g Exp)) -> Exp -> f (g Exp)
everywhereM f x = (<|>) <$> f x <*> getCompose (traverseChildren (Compose . everywhereM f) x)

everywhere :: Alternative f => (Exp -> f Exp) -> Exp -> f Exp
everywhere f = runIdentity . everywhereM (Identity . f)

-- Track ways to change part of an expression
data Change a = Change { changeOrig :: a, changeNew :: [a] }
  deriving (Functor)
instance Applicative Change where
  pure x = Change x []
  Change x xs <*> Change y ys = Change (x y) (map ($y) xs ++ map x ys)
instance Alternative Change where
  empty = error "only (<|>)"
  Change x xs <|> Change _ ys = Change x (xs ++ ys)

testChange :: Eq a => (a -> a) -> (a -> Change a)
testChange f x = let x' = f x
                 in Change x [x' | x' /= x ]

tryEvalHere :: EvalEnv -> Exp -> Change Exp
tryEvalHere e = testChange (eval e{evalStrategy = OneStep})

-- all possible ways to take a single evaluation step
-- used to test confluence
evalEverywhere :: EvalEnv -> Exp -> [Exp]
evalEverywhere e x = changeNew $ everywhere (tryEvalHere e) x

--------------------------------------------------------------------------------
-- Evaluation from Tc monad
--------------------------------------------------------------------------------

tcEvalEnv :: EvalStrategy -> TcM EvalEnv
tcEvalEnv s = do
  mv <- metaValues
  return $ EvalEnv
    { evalStrategy = s
    , evalMetaValue = mv
    }

tcEval :: EvalStrategy -> Exp -> TcM Exp
tcEval s x = flip eval x <$> tcEvalEnv s

