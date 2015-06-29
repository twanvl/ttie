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
import EqZipper

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
eval (evalStrategy->WHNF) x@(Pair _ _ _ _) = x
eval (evalStrategy->WHNF) x@(Binder _ _ _) = x
eval e (Meta x xs) = evalMeta e x xs
eval (evalStrategy->MetaOnly) x = x
eval e (TypeSig x _ty) = evalMore e x
eval e x = evalHere e $ mapChildren (evalMore e) x

evalHere :: EvalEnv -> Exp -> Exp
evalHere e (TypeSig x _ty)  = evalMore  e x
evalHere e (App x y)        = evalApp   e x y
evalHere e (Proj h p x)     = evalProj  e h p x
evalHere e (SumElim x ys z) = evalCase  e x ys z
evalHere e (IFlip x)        = evalIFlip e x
evalHere e (IAnd x y)       = evalIAnd  e x y
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
evalApp _ x y = App x y

evalProj :: EvalEnv -> Hiding -> Proj -> Exp -> Exp
evalProj e _ Proj1 (Pair _ x _y _) = evalMore e x
evalProj e _ Proj2 (Pair _ _x y _) = evalMore e y
evalProj _ h p x = Proj h p x

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

evalIAnd :: EvalEnv -> Exp -> Exp -> Exp
evalIAnd _ I1 _ = I1
evalIAnd _ I2 y = y
evalIAnd _ _ I1 = I1
evalIAnd _ x I2 = x
-- commutativity and idempotence?
evalIAnd _ x y = IAnd x y

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
evalCast e (Bound i a) i1 i2 x = 
  cevWrappedValue $ evalCast' e i a i2 x'
  where
  x' = CastEqValue
      { cevValue = x
      , cevPath = []
      , cevCurrentIdx = i1
      }
{-
--evalCast _ _ I1 I1 y = y
--evalCast _ _ I2 I2 y = y
evalCast _ _ j1 j2 y | j1 == j2 = y
evalCast _ (NotBound _) _ _ y = y
--
{-evalCast e [qq|[$i](Pi (Arg $h a) [$x]b)|] j1 j2 y = evalMore e
  [qq| Lam (Arg $h a[i=j2[]]) [$x]
       (Cast ([$i]b[i,x=Cast ([$i]a[i]) j2[] i x]) j1[] j2[]
             (App y[] (Arg $h (Cast ([$i]a[i]) j2[] j1[] x)))) |]
-}
--
{-
evalCast e [qq|[$i](Si (Arg $h a) [$x]b)|] j1 j2 y = evalMore e
  [qq| Pair (Arg $h (Cast [$i]a j1[] j2[] (Proj (Arg $h Proj1) y)))
                    (Cast [$i]b[i,x=Cast [$i]a[i] j1[] i (Proj (Arg $h Proj1) y[])]
                          j1[] j2[] (Proj (Arg $h Proj2) y))
            (Si (Arg $h a[i=j2[]]) [$x]b[i=j2[],x]) |]
-}
--
evalCast e (Bound i (Pi (Arg h a) (Bound x b))) j1 j2 f =
  Lam (Arg h (subst1 j2 a)) (Bound x fx'')
  where
  x'   = evalCast e (Bound i $ raiseAtBy 1 1 a) (raiseBy 1 j2) (raiseBy 1 j1) (Var 0)
  xi   = evalCast e (Bound i $ raiseAtBy 1 2 a) (raiseBy 2 j2) (Var 0)        (Var 1)
  fx'  = App (raiseBy 1 f) (Arg h x')
  fx'' = evalCast e (Bound i $ raiseSubsts 2 [xi, Var 0] b) (raiseBy 1 j1) (raiseBy 1 j2) fx'
--
evalCast e (Bound i (Si (Arg h a) b)) j1 j2 y =
  Pair h y1' y2' (Si (Arg h (subst1 j2 a)) (fmap (substRaiseAt 1 j2) b))
  where
  proj1 = evalProj e h Proj1
  proj2 = evalProj e h Proj2
  y1 = proj1 y
  y2 = proj2 y
  y1' = evalCast e (Bound i a) j1 j2 y1
  y1i = evalCast e (Bound i $ raiseAtBy 1 1 a) (raiseBy 1 j1) (Var 0) (raiseBy 1 y1)
  y2' = evalCast e (Bound i $ substBound b y1i) j1 j2 y2
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
  [qq| Refl [$j](Pair $h w1[i2=i2[],j]
                         w2[i2=i2[],j]
                      (Si (Arg $h a[i=i2[],j=j]) [$x]b[i=i2[],j=j,x])) |]
  where
  yk = [qq|[~j](IV u[i=i1[]] v[i=i1[]] y[] j)|] :: Wrap "j" Exp
  y1 = [qq|Refl [$j](Proj $h Proj1 yk)|]
  y2 = [qq|Refl [$j](Proj $h Proj2 yk)|]
  z1 = [qq|[~i2]Cast [$i](Eq [$j]a[i,j]              u1[i] v1[i]) i1[] i2 y1[]|]
  z2 = [qq|[~i2]Cast [$i](Eq [$j]b[i,j,x=w1[i2=i,j]] u2[i] v2[i]) i1[] i2 y2[]|]
  w1 = [qq|[~i2][~j] (IV u1[i=i2] v1[i=i2] z1[i2=i2] j)|]
  w2 = [qq|[~i2][~j] (IV u2[i=i2] v2[i=i2] z2[i2=i2] j)|]
  u1 = [qq|[~i]Proj $h Proj1 u|] :: Wrap "i" Exp
  u2 = [qq|[~i]Proj $h Proj2 u|]
  v1 = [qq|[~i]Proj $h Proj1 v|]
  v2 = [qq|[~i]Proj $h Proj2 v|]
--
--evalCast s [qq|[$i]a|] I2 j2 x = evalMore s [qq| Cast [$i]a[i=IFlip i] I1 (IFlip j2) x |]
--
evalCast _ a j1 j2 x = Cast a j1 j2 x
-}

-- reduction of "Cast (Bound i (ezType p a)) i1 i2 x"
evalCast' :: EvalEnv -> Name -> Exp -> Exp -> CastEqValue -> CastEqValue
evalCast' _ _ _ i2 x | cevCurrentIdx x == i2 = x
evalCast' e i (Eq (Bound j a) u v) i2 x =
  evalCast' e i a i2 (cevPush j u v x)
evalCast' _ _ a i2 x | not (cevIndexIsFree x) && not (isFree (cevDepth x) a) = x'
  where
  x' = x { cevCurrentIdx = i2 }
evalCast' e i (Si (Arg h a) b) i2 x = x12''
  where
  proj1 = evalProj e h Proj1
  proj2 = evalProj e h Proj2
  x1 = cevMap proj1 x
  x2 = cevMap proj2 x
  x1' = evalCast' e i a i2 x1
  x1i = evalCast' e i (raiseAtBy (cevDepth x+1) 1 a) (Var 0) (cevRaiseBy 1 x1)
  x2' = evalCast' e i (substBound b (cevUnwrappedValue 0 x1i)) i2 x2
  ab' = substRaiseAt (cevDepth x) i2 (Si (Arg h a) b)
  x12' = cevZipWith (\u v -> Pair h u v ab') x1' x2'
  x12'' = x12' { cevPath  = cevPath x }
evalCast' e i (Pi (Arg h a) b) i2 f {-|
  traced ("  a   = " ++ showWithNames (js++"i":gamma) a ++ "\n" ++
          "  b   = " ++ showWithNames (js++"i":gamma) b ++ "\n" ++
          "  f   = " ++ showWithNames gamma f ++ "\n" ++
          "  i2' = " ++ showWithNames (js++gamma) (raiseBy (cevDepth f) i2) ++ "\n" ++
          "  a'  = " ++ showWithNames (js++gamma) a' ++ "\n" ++
          --"  x   = " ++ showWithNames (js'++"x":js++gamma) xV ++ "\n" ++
          "  x   = " ++ showWithNames ("x":js++gamma) x ++ "\n" ++
          "  xi  = " ++ showWithNames ("i":"x":js++gamma) xi ++ "\n" ++
          "  xi' = " ++ showWithNames (js'++"i":"x":js++gamma) (cevUnwrappedValue 0 xi) ++ "\n" ++
          --"  f'  = " ++ showWithNames ("x":js++gamma) f' ++ "\n" ++
          "  f x = " ++ showWithNames ("x":js++gamma) fx ++ "\n" ++
          "  b'  = " ++ showWithNames (js'++"i":"x":js++gamma) b' ++ "\n" ++
          "  b'x = " ++ showWithNames (js'++"i":"x":js++gamma) b'x ++ "\n" ++
          "  fx' = " ++ showWithNames ("x":js++gamma) fx' ++ "\n" ++
          "  fxU = " ++ showWithNames (js'++"x":js++gamma) (cevUnwrappedValue 0 fx') ++ "\n" ++
          "  fxJ = " ++ showWithNames ("x":js++gamma) fx'' ++ "\n" ++
          "  f'' = " ++ showWithNames (gamma) f'' ++ "\n" ++
          ""
  ) True-}
  = f''
  where
  i1 = cevCurrentIdx f
  js = cevNames f
  x  = cevConvertValue js 1 a (raiseBy (cevDepth f+1) i2) (raiseBy (cevDepth f+1) i1) (Var 0)
  xi = cevConvertValue js 2 a (raiseBy (cevDepth f+2) i2) (Var 0) (Var 1)
  f' = cevRaiseBy (cevDepth f + 1) f
  fx = cevZipWith (\u v -> App u (Arg h v)) f' x
  b' = raiseAtBy (cevDepth f+2) (cevDepth f+1) <$> b
  b'x = substBound b' (cevUnwrappedValue 0 xi)
  fx' = evalCast' e i b'x (raiseBy (cevDepth f+1) i2) fx
  fx'' = joinVariables 1 (cevDepth f) $ cevUnwrappedValue 0 fx'
  a' = substAt (cevDepth f) (raiseBy (cevDepth f) i2) a
  f'' = CastEqValue
    { cevValue = evalMore e $ ezWrapNames (cevNames f) $ Lam (Arg h a') $ Bound (boundName b) fx''
    , cevPath  = cevPath f
    , cevCurrentIdx = i2
    }
evalCast' _ i a i2 x = x'
  where
  x' = x
    { cevValue = Cast (Bound i (cevType a x)) (cevCurrentIdx x) i2 (cevWrappedValue x)
    , cevCurrentIdx = i2
    }

  
-- Eta contractions
etaContract :: Exp -> Exp
etaContract (Pair h1 (Proj h2 Proj1 x) (Proj h3 Proj2 y) _) -- Note: only valid if the types are right!
  | x == y && h1 == h2 && h1 == h3 = x
etaContract [qq|Lam (Arg h _) [$_x](App f[] (Arg $h' _x))|] | h == h' = f
etaContract [qq|Refl [$_i](IV _ _ x[] _i)|] = x
etaContract x = x

--------------------------------------------------------------------------------
-- Is an expression in WHNF?
--------------------------------------------------------------------------------

isWHNF :: Exp -> Bool
isWHNF (TypeSig _ _) = False
isWHNF (App (Lam _ _) _) = False
isWHNF (App x _) = isWHNF x
isWHNF (Proj _ _ (Pair _ _ _ _)) = False
isWHNF (Proj _ _ x) = isWHNF x
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

