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

import qualified Data.Map as Map

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

data EvalStrategy = WHNF | NF | MetaOnly | OneStep
  deriving (Eq)

data EvalEnv = EvalEnv
  { evalStrategy  :: EvalStrategy
  , evalMetaValue :: MetaVar -> Seq Exp -> Maybe Exp
  , evalGlobal :: Name -> Maybe Exp
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
evalHere e (Free x) | Just val <- evalGlobal e x = evalMore e val
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

-- reduction of "Cast (Bound i (ezType p a)) i1 i2 x"
evalCast' :: EvalEnv -> Name -> Exp -> Exp -> CastEqValue -> CastEqValue
--evalCast' _ _ _ i2 x | cevCurrentIdx x == i2 && i2 `elem` [I1,I2] = x
evalCast' _ _ _ i2 x | cevCurrentIdx x == i2 = x
evalCast' e i (Eq (Bound j a) u v) i2 x =
  evalCast' e i a i2 (cevPush j u v x)
evalCast' _ _ a i2 x | not (cevIndexIsFree x) && not (isFree (cevDepth x) a) = x' -- We don't actually need this.
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
  vals <- freeValues
  return $ EvalEnv
    { evalStrategy = s
    , evalMetaValue = mv
    , evalGlobal = vals
    }

tcEval :: EvalStrategy -> Exp -> TcM Exp
tcEval s x = flip eval x <$> tcEvalEnv s

