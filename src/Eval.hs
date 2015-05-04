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

type NfExp = Exp
data EvalStrategy = WHNF | NF | MetaOnly | OneStep
  deriving (Eq)

eval :: EvalStrategy -> Exp -> TcM Exp
eval WHNF x@(Pair _ _ _) = pure x
eval WHNF x@(Binder _ _ _) = pure x
eval s (Meta x xs) = evalMeta s x xs
eval MetaOnly x = pure x
eval s (TypeSig x _ty) = evalMore s x
eval s x = evalHere s =<< traverseChildren (evalMore s) x

evalHere :: EvalStrategy -> Exp -> TcM Exp
evalHere s (TypeSig x _ty) = evalMore s x
evalHere s (App x y) = evalApp s x y
evalHere s (Proj x y) = evalProj s x y
evalHere s (SumElim x ys z) = evalCase s x ys z
evalHere s (IFlip x) = evalIFlip s x
evalHere s (IV x y z w) = evalIV s x y z w
evalHere s (Eq x y z) = evalEq s x y z
evalHere s (Cast x y z w) = evalCast s x y z w
evalHere NF x = pure $ etaContract x
evalHere _ x = pure x

evalMore :: EvalStrategy -> Exp -> TcM Exp
evalMore OneStep x = pure x
evalMore s x = eval s x

evalMeta :: EvalStrategy -> MetaVar -> Seq Exp -> TcM Exp
evalMeta s x xs = do
  m <- metaValue x xs
  case m of
    Nothing -> Meta x <$> mapM (eval s) xs
    Just m' -> eval s m'

evalApp :: EvalStrategy -> Exp -> Arg Exp -> TcM Exp
evalApp s (Lam _ x) y = evalMore s $ substBound x (argValue y)
--evalApp s (Refl x `AppH` y `AppH` z) (Arg h w) = Refl (App x (Arg h (IV)))
--evalApp s [qq| Refl [$n]x `AppH` y `AppH` z|] (Arg h w) =
--  evalMore s $ [qq| Refl [$n](App x (Arg $h (IV y[] z[] w[] n))) |]
evalApp _ x y = pure $ App x y

evalProj :: EvalStrategy -> Arg Proj -> Exp -> TcM Exp
evalProj s (Arg _ Proj1) (Pair x _y _) = evalMore s (argValue x)
evalProj s (Arg _ Proj2) (Pair _x y _) = evalMore s y
--evalProj s p (Refl x) = Refl <$> traverseBound Interval (evalProj s p) x
evalProj _ p x = pure $ Proj p x

evalCase :: EvalStrategy -> Exp -> [SumCase] -> Exp -> TcM Exp
evalCase s (SumVal n x _) ys _
  | Just (SumCase _ _ y) <- find ((n==) . caseName) ys
  = evalMore s (substBound y x)
evalCase _ x ys a = pure $ SumElim x ys a

evalIFlip :: EvalStrategy -> Exp -> TcM Exp
evalIFlip _ I1 = pure I2
evalIFlip _ I2 = pure I1
evalIFlip _ (IFlip x) = pure $ x
evalIFlip _ x  = pure $ IFlip x

evalIV :: EvalStrategy -> Exp -> Exp -> Exp -> Exp -> TcM Exp
evalIV _ x _ _ I1 = pure x
evalIV _ _ y _ I2 = pure y
evalIV _ _ _ I12 w = pure w
evalIV s _ _ (Refl z) w = evalMore s $ substBound z w
evalIV _ x y z w  = pure $ IV x y z w

evalEq :: EvalStrategy -> Bound Exp -> Exp -> Exp -> TcM Exp
{-
evalEq s [qq| [$i] Si (Arg $h a) ([$n] b) |] y z = do
  evalMore s [qq| Si (Arg $h (Eq [$i]a (Proj (Arg $h Proj1) y[]) (Proj (Arg $h Proj1) z[])))
                 [$n](Eq [$i]b[i=i,n=IV (Proj (Arg $h Proj1) y[]) (Proj (Arg $h Proj1) z[]) n i]
                           (Proj (Arg $h Proj2) y[]) (Proj (Arg $h Proj2) z[])) |]
  {-
  aEq <- [qq| %evalEq s [$i]a (Proj (Arg $h Proj1) y[]) (Proj (Arg $h Proj1) z[]) |]
  bEq <- [qq| [%n:aEq] %evalEq $s [$i]b[i=i,n=IV (Proj (Arg $h Proj1) y[]) (Proj (Arg $h Proj1) z[]) n i]
              (Proj (Arg $h Proj2) y[]) (Proj (Arg $h Proj2) z[])|]
  return $ Si (Arg h aEq) bEq-}
evalEq s [qq| [$i] Pi (Arg $h a) ([$n] b) |] y z = do
  let n1 = nameVariant n "1"
  let n2 = nameVariant n "2"
  evalMore s $
    [qq| Pi (%hidden a[i=I1]) [$n1](
         Pi (%hidden a[i=I2]) [$n2](
         Pi (Arg $h (Eq [$i]a[i=i] n1 n2)) [$n](
         Eq [$i]b[i=i,n=IV n1 n2 n i] (App y[] (Arg $h n1)) (App z[] (Arg $h n2))))) |]
evalEq _ [qq| [$_i] UnitTy |] _ _ = pure UnitTy
-}
evalEq _ x y z = pure $ Eq x y z

--evalFw s [qq|Refl [$_n]x[] |] y = y
evalCast :: EvalStrategy -> Bound Exp -> Exp -> Exp -> Exp -> TcM Exp
evalCast _ _ I1 I1 y = return y
evalCast _ _ I2 I2 y = return y
evalCast _ (NotBound _) _ _ y = return y
--
evalCast s [qq|[$i](Pi (Arg $h a) [$x]b)|] j1 j2 y = evalMore s
  [qq| Lam (Arg $h a[i=$j2]) [$x]
       (Cast ([$i]b[i,x=Cast ([$i]a[i]) $j2 $j1 x]) $j1 $j2
             (App y[] (Arg $h (Cast ([$i]a[i]) $j2 $j1 x)))) |]
--
evalCast s [qq|[$i](Si (Arg $h a) [$x]b)|] j1 j2 y = evalMore s
  [qq| Pair (Arg $h (Cast [$i]a $j1 $j2 (Proj (Arg $h Proj1) y)))
                    (Cast [$i]b[i,x=Proj (Arg $h Proj1) y[]] $j1 $j2 (Proj (Arg $h Proj2) y))
            (Si (Arg $h a[i=$j2]) [$x]b[i=$j2,x]) |]
--
--evalCast s [qq|(Bound i (Eq a x y))|] [qq|Refl (Bound _ z)|] = evalFwRefl i a x y z
evalCast s [qq|[$i](Eq [$_j]_a[_j] _x[] y)|] I1 I2 [qq|Refl (NotBound _)|] = evalMore s
  [qq| Refl [$i]y[i] |]
--
evalCast _ a j1 j2 x = pure $ Cast a j1 j2 x

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
everywhere :: (MonadBound Exp f, Alternative g) => (Exp -> f (g Exp)) -> Exp -> f (g Exp)
everywhere f x = (<|>) <$> f x <*> getCompose (traverseChildren (Compose . everywhere f) x)

-- Track ways to change part of an expression
data Change a = Change { changeOrig :: a, changeNew :: [a] }
  deriving (Functor)
instance Applicative Change where
  pure x = Change x []
  Change x xs <*> Change y ys = Change (x y) (map ($y) xs ++ map x ys)
instance Alternative Change where
  empty = error "only (<|>)"
  Change x xs <|> Change _ ys = Change x (xs ++ ys)

tryEvalHere :: Exp -> TcM (Change Exp)
tryEvalHere x = do
  x' <- eval OneStep x
  return $ Change x [x' | x'/=x]

-- all possible ways to take a single evaluation step
-- used to test confluence
evalEverywhere :: Exp -> TcM [Exp]
evalEverywhere x = changeNew <$> everywhere tryEvalHere x

