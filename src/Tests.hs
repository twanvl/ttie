{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DefaultSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Main where

import Prelude ()
import Util.MyPrelude
import Util.PrettyM
import Util.Parser
import Syntax
import Substitution
import Names
import TcMonad
import Typing
import Eval

import qualified Data.Map as Map
import Data.Typeable
import Data.String
import Data.List (isPrefixOf)

import Test.Tasty
import Test.Tasty.Providers
import qualified Control.Exception as E
import System.IO

--------------------------------------------------------------------------------
-- Environment with some names
--------------------------------------------------------------------------------

testDecls :: Map Name Decl
testDecls = Map.fromList
  [("A",    Postulate $ pe "Set")
  ,("B",    Postulate $ pe "Set")
  ,("x",    Postulate $ pe "A")
  ,("y",    Postulate $ pe "A")
  ,("xy",   Postulate $ pe "Eq A x y")
  ,("f",    Postulate $ pe "A -> B")
  ,("B'",   Postulate $ pe "A -> Set")
  ,("f'",   Postulate $ pe "(x:A) -> B' x")
  ,("ab",   Postulate $ pe "Eq Set A B")
  ,("Nat",  Postulate $ pe "Set")
  ,("zero", Postulate $ pe "Nat")
  ,("suc",  Postulate $ pe "Nat -> Nat")
  ]
  -- "Nat", pe "Set", pe "x:data{zero;suc} * case x of {zero -> data{unit}; suc -> Nat}"
  -- "Nat", pe "Set", pe "data{zero:Unit;suc:Nat}"
  -- "zero", , pe "con{zero}"

testCtx :: TcCtx
testCtx = emptyCtx
  { ctxDecls = testDecls
  }

--------------------------------------------------------------------------------
-- Expressions to test
--------------------------------------------------------------------------------

-- expressions that should typecheck
goodExpressions :: [String]
goodExpressions =
  ["\\(x:A). x"
  ,"proj1 (x,y)"
  ,"proj2 (x,y)"
  ,"f x"
  ,"{A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)"
  ,"(\\{A} x -> x) : {A : Set} -> (A -> A)"
  ,"(\\{A} {B} f x -> f x) : {A B : Set} -> (A -> B) -> (A -> B)"
  ,"(\\{A} {B} {C} f g x -> f (g x)) : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)"
  ,"(\\f g x -> f (g x)) : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)"
  ,"refl (x,x)"
  ,"01"
  ,"refl_i (\\(x:(refl Nat)^i) -> x)"
  ,"proj2 ({x} , x , f) x"
  -- sums
  ,"data{zero:Unit; suc:Nat}"
  ,"(\\x -> case x of {zero _ -> zero; suc x -> x}) : data{zero:Unit; suc:Nat} -> Nat"
  ,"refl _ : Eq _ x (case value left tt of {left _ -> x; right (_:Unit) -> y})"
  ,"(\\x -> case x of {}) : data{} -> {A : Set} -> A"
  ,"(\\ft -> fw_i (case ft^i of {false _ -> Unit; true _ -> data{}}) tt)"
   ++": Eq data{false:Unit;true:Unit} (value false tt) (value true tt) -> data{}" -- false /= true
   -- type inference
  ,"((\\{A:Type} (x : A) -> x) (tt,tt)) : Unit * Unit"
  ,"((\\{A:Type} x -> value wrap x : data{wrap:A}) (tt,tt)) : data {wrap : Unit * Unit}"
  ,"Unit : _ : _ : _ : _ : _ : _"
  -- OTT
  {-
  ,"proj1 (refl (x,y))"
  ,"(refl f') {_} {_} (refl x)"
  ,"(refl f') xy"
  ,"(\\x y -> tt) : (x y : Unit) -> Eq _ x y"
  -}
  ,"(\\xx' -> refl_i (f xx'^i)) : forall {x x'}. Eq A x x' -> Eq _ (f x) (f x')"
  -- and
  -- casts
  ,"{-subst-} (\\P xy px -> fw_i (P xy^i) px)"
   ++": {A : Set} -> (P : A -> Set) -> {x y : A} -> Eq _ x y -> P x -> P y"
  ,"{-bw-fw-} (\\x -> refl_i (cast_j ab^j i 0 (cast_j ab^j 0 i x)))"
   ++" : forall x. Eq _ x (bw_i ab^i (fw_i ab^i x))"
  ,"{-eq-fw-} (\\x -> refl_i (cast_j ab^j 0 i x))"
   ++" : forall x. Eq_i ab^i x (fw_i ab^i x)"
  --,"{-jay-} (\\{A} {x} P xy px -> fw_i (P xy^i (cast_j (Eq _ x xy^j) 0 i (refl x))) px)"
  -- ++" : {A : Set} -> {x : A} -> (P : (y : A) -> Eq A x y -> Set) -> {y : A} -> (xy : Eq A x y) -> P x (refl x) -> P y xy"
  --,"{-jay-inline-} \\{A : Set} {x} (P : (y : A) -> Eq A x y -> Set) {y} (xy : Eq A x y) px ->\
  --   \ fw_i (P xy^i (cast_j (Eq A x xy^j) 0 i (refl x))) px : P y xy"
  --,"{-jay-alt-} \\{A : Set} {x} (P : (y : A) -> Eq A x y -> Set) {y} (xy : Eq A x y) px ->\
  --   \ fw_i (P xy^i (cast_j (Eq A xy^j xy^i) i 0 (refl xy^i))) px : P y xy"
  ,"{-jay-and-} \\{A : Set} {x} (P : (y : A) -> Eq A x y -> Set) {y} (xy : Eq A x y) px ->\
     \ fw_i (P xy^i (refl_j xy^(iand i j))) px : P y xy"
  --,"{-jay-and2-} \\{A : Set} {x} (P : (y : A) -> Eq A x y -> Set) {y} (xy : Eq A x y) px ->\
  --   \ fw_i (P xy^i (refl_j xy^((cast_j (Eq Interval 0 j) 0 j (refl 0))^i))) px : P y xy"
  --,"{-jay-and2b-} \\{A : Set} {x} (P : (y : A) -> Eq A x y -> Set) {y} (xy : Eq A x y) px ->\
  --   \ fw_i (P xy^i (refl_j xy^((cast_j (Eq Interval 0 j) 1 j (refl_j j))^i))) px : P y xy"
  --,"{-jay-and3-} \\{A : Set} {x} (P : (y : A) -> Eq A x y -> Set) {y} (xy : Eq A x y) px ->\
  --   \ fw_i (P xy^i (refl_j xy^((cast_j (Eq Interval 0 j) 0 i (refl 0))^j))) px : P y xy"
  --,"{-jay-and3b-} \\{A : Set} {x} (P : (y : A) -> Eq A x y -> Set) {y} (xy : Eq A x y) px ->\
  --   \ fw_i (P xy^i (refl_j xy^((cast_j (Eq Interval 0 j) 1 i (refl_i i))^j))) px : P y xy"
  -- equivalence to OTT style
  ,"{-ott-app-} \\{A : Interval -> Set} {B : forall i. A i -> Set} {f : (x : A 0) -> B 0 x} {g : (x : A 1) -> B 1 x} -> (\
     \(\\fg x12 -> refl_i (fg^i x12^i))\
     \: Eq_i ((x : A i) -> B i x) f g -> (forall {x1 x2} (x12 : Eq_i (A i) x1 x2) -> Eq_i (B i x12^i) (f x1) (g x2)))"
  ,"{-ott-lam-} \\{A : Interval -> Set} {B : forall i. A i -> Set} {f : (x : A 0) -> B 0 x} {g : (x : A 1) -> B 1 x} -> (\
     \(\\fg -> refl_i (\\x -> (fg {cast_k (A k) i 0 x} {cast_k (A k) i 1 x} (refl_j (cast_k (A k) i j x)))^i))\
     \: (forall {x1 x2} (x12 : Eq_i (A i) x1 x2) -> Eq_i (B i x12^i) (f x1) (g x2)) -> Eq_i ((x : A i) -> B i x) f g)"
  {-,"{-ott-lam2-} \\{A : Interval -> Set} {B : forall i. A i -> Set} {f : (x : A 0) -> B 0 x} {g : (x : A 1) -> B 1 x} -> (\
     \(\\fg -> refl_i (\\x -> (fg {cast_k (A k) i 0 x} {cast_k (A k) i 1 x}\
     \    (cast_k (Eq_i (A (iand i k)) (cast_l (A l) i 0 x) \
     \                                 (cast_l (A l) i k x)) \
     \            0 1 (refl (cast_l (A l) i 0 x)) ) \
     \)^i))\
     \: (forall {x1 x2} (x12 : Eq_i (A i) x1 x2) -> Eq_i (B i x12^i) (f x1) (g x2)) -> Eq_i ((x : A i) -> B i x) f g)"-}
  -- type checking of evaluation steps
  ,"forall (A : _ -> Set) j x. Eq _ (cast_i (A i) j j x) x"
  ,"{-ty-cast-pair-} \\(A : _ -> Set) (B : ∀ {x}. A x -> Set) j1 j2 xy. \
     \ (cast_i ((x:A i) * B x) j1 j2 xy : (x:A j2)*B x)"
  ,"{-ty-cast-fun-} \\(A : _ -> Set) (B : ∀ {x}. A x -> Set) j1 j2 xy. \
     \ (cast_i ((x:A i) -> B x) j1 j2 xy : (x:A j2)->B x)"
  ,"{-ty-cast-eq-pair-} \
     \\\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v j1 j2 (xy : Eq_j ((x:A j1 j)*B x) (u j1) (v j1)). \
     \ (cast_i (Eq_j ((x:A i j)*B x) (u i) (v i)) j1 j2 xy : Eq_j ((x:A j2 j)*B x) (u j2) (v j2))"
  ,"{-ty-cast-eq-fun-} \
     \\\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v j1 j2 (xy : Eq_j ((x:A j1 j)->B x) (u j1) (v j1)). \
     \ (cast_i (Eq_j ((x:A i j)->B x) (u i) (v i)) j1 j2 xy : Eq_j ((x:A j2 j)->B x) (u j2) (v j2))"
  ,"{-ty-cast-eq-eq-pair-} \
     \\\(A : _ -> _ -> _ -> Set) (B : ∀ {i j k}. A i j k -> Set) u v p q j1 j2 \
     \  (xy : Eq_j (Eq_k ((x:A j1 j k)*B x) (u j1 j) (v j1 j)) (p j1) (q j1)). \
     \ (cast_i (Eq_j (Eq_k ((x:A i j k)*B x) (u i j) (v i j)) (p i) (q i)) j1 j2 xy \
     \ : Eq_j (Eq_k ((x:A j2 j k)*B x) (u j2 j) (v j2 j)) (p j2) (q j2))"
  ,"{-ty-cast-eq-eq-fun-} \
     \\\(A : _ -> _ -> _ -> Set) (B : ∀ {i j k}. A i j k -> Set) u v p q j1 j2 \
     \  (xy : Eq_j (Eq_k ((x:A j1 j k)->B x) (u j1 j) (v j1 j)) (p j1) (q j1)). \
     \ (cast_i (Eq_j (Eq_k ((x:A i j k)->B x) (u i j) (v i j)) (p i) (q i)) j1 j2 xy \
     \ : Eq_j (Eq_k ((x:A j2 j k)->B x) (u j2 j) (v j2 j)) (p j2) (q j2))"
  -- implementation of casts
  ,"{-cast-pair-} \\(A : _ -> Set) (B : ∀ {x}. A x -> Set) j1 j2 xy. \
     \ refl _ : Eq ((x:A j2)*B x) \
     \             (cast_i ((x:A i) * B x) j1 j2 xy) \
     \             (cast_i (A i) j1 j2 (proj1 xy)\
     \             ,cast_i (B {i} (cast_i' (A i') j1 i (proj1 xy))) j1 j2 (proj2 xy))"
  ,"{-cast-fun-} \\(A : _ -> Set) (B : ∀ {x}. A x -> Set) j1 j2 xy. \
     \ refl _ : Eq ((x:A j2) -> B x) \
     \             (cast_i ((x:A i) -> B x) j1 j2 xy) \
     \             (\\(x:A j2) -> cast_i (B {i} (cast_i (A i) j2 i x)) j1 j2 (xy (cast_i (A i) j2 j1 x)) )"
  ,"{-cast-eq-pair-} \\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v j1 j2 (xy : Eq_j ((x:A j1 j)*B x) (u j1) (v j1)). \
     \ refl _ : Eq (Eq_j ((x:A j2 j)*B x) (u j2) (v j2)) \
     \             (cast_i (Eq_j ((x:A i j)*B x) (u i) (v i)) j1 j2 xy) \
     \             (refl_j ((cast_i (Eq_j (A i j) (proj1 (u i)) (proj1 (v i))) j1 j2 (refl_j (proj1 xy^j)))^j \
     \                     ,(cast_i (Eq_j (B {i} {j} \
     \                      (cast_i (Eq_j (A i j) (proj1 (u i)) (proj1 (v i))) j1 i (refl_j (proj1 xy^j)))^j) \
     \                                    (proj2 (u i)) (proj2 (v i))) j1 j2 (refl_j (proj2 xy^j)))^j : (x:A j2 j)*B x))"
  -- cast (Eq (A*B))
  {-,"\\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v j1 j2 (xy : Eq_j ((x:A j1 j)*B x) (u j1) (v j1)). \
     \refl_j (iv (proj1 (u j2)) (proj1 (v j2)) \
     \           (cast_i (Eq_j (A i j) (proj1 (u i)) (proj1 (v i))) j1 j2 (refl_j (proj1 (iv (u j1) (v j1) xy j)))) \
     \           j, \
     \ iv _ _ (cast_i (Eq_j (B {i} {j} (iv _ _ (cast_i (Eq_j (A i j) (proj1 (u i)) (proj1 (v i))) j1 i (refl_j (proj1 (iv (u j1) (v j1) xy j)))) j)) (proj2 (u i)) (proj2 (v i))) j1 j2 (refl_j (proj2 (iv (u j1) (v j1) xy j)))) j : (x:A j2 j) * B x)"-}
  ,"\\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v j1 j2 (xy : Eq_j ((x:A j1 j)*B x) (u j1) (v j1)). \
     \refl_j ((cast_i (Eq_j (A i j) (proj1 (u i)) (proj1 (v i))) j1 j2 (refl_j (proj1 xy^j)))^j \
     \       ,(cast_i (Eq_j (B {i} {j} \
     \        (cast_i (Eq_j (A i j) (proj1 (u i)) (proj1 (v i))) j1 i (refl_j (proj1 xy^j)))^j) \
     \                              (proj2 (u i)) (proj2 (v i))) j1 j2 (refl_j (proj2 xy^j)))^j : (x:A j2 j) * B x)"
  {-,"\\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v j1 j2 (xy : Eq_j ((x:A j1 j)*B x) (u j1) (v j1)). \
     \refl_j (cast_i (A i j) j1 j2 (proj1 (iv (u j1) (v j1) xy j))), \
     \refl_j (iv _ _ (cast_i (Eq_j (A i j) (proj1 (u i)) (proj1 (v i))) j1 j2 (refl_j (proj1 (iv (u j1) (v j1) xy j)))) j)"
  
  ,"{-si-eq-}\\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v j1 j2 (xy : Eq_j ((x:A j1 j)*B x) (u j1) (v j1)). \
     \refl_j ((cast_i (Eq_j (A i j) (proj1 (u i)) (proj1 (v i))) j1 j2 (refl_j (proj1 xy^j)))^j),\
     \refl_j (cast_i (A i j) j1 j2 (proj1 xy^j)),\
     \refl_j (cast_i (Eq_k (A i k) (cast_i (A i 0) j1 i (cast_j (A j1 j) j 0 (proj1 xy^j))) \
     \                             (cast_i (A i 1) j1 i (cast_j (A j1 j) j 1 (proj1 xy^j)))) j1 j2 \
     \               (refl_k (cast_j (A j1 j) j k (proj1 xy^j))))^j,\
     \refl_j (cast_i (Eq_k (A i k) (proj1 (u i)) \
     \                             (proj1 (v i)))  j1 j2 \
     \               (refl_k (cast_j (A j1 j) j k (proj1 xy^j))))^j,\
     \refl_j (cast_i (Eq_k (A i k) (cast_i (A i 0) j1 i (proj1 xy^0)) \
     \                             (cast_i (A i 1) j1 i (proj1 xy^1))) j1 j2 \
     \               (refl_k (proj1 xy^k)) )^j"
  -}
  -- cast (Eq (A->B))
  ,"{-ar-eq-}\\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v j1 j2 (xy : Eq_j ((x:A j1 j)->B x) (u j1) (v j1)). \
     \ refl_j (\\(x:A j2 j) -> cast_i (B {i} {j} (cast_i (A i j) j2 i x)) j1 j2 (xy^j (cast_i (A i j) j2 j1 x)) ), \
     \  refl_j (\\(x:A j2 j) -> xy^j (cast_i (A i j) j2 j1 x) ), \
     \  refl_j (\\(x:A j2 j) -> refl_k (cast_j (A j2 j) j k x) ){-, \
     \  refl_j (\\(x:A j2 j) -> cast_i (Eq_j (A i j) (cast_j (A i j) j2 0 x) (cast_j (A i j) j2 0 x)) j2 j1 (refl_k (cast_k (A j2 j) j k x)) )-}"
  {-,"{-ar-ty-} \\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) (j1 j2 j : Interval) x. \
     \\\(y : B {j1} {j} (cast_i (A i j) j2 j1 x)) -> \
     \  cast_i (B {i} {j} (cast_i (A i j) j2 i x)) j1 j2 y"
  ,"{-ar-ott1-} \\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v (j1 j2 : Interval) (xy : Eq_j ((x:A j1 j)->B x) (u j1) (v j1)). \
     \\\{x1} {x2} (x12 : Eq_j (A j1 j) (cast_i (A i 0) j2 j1 x1) (cast_i (A i 1) j2 j1 x2)) -> refl_i (xy^i x12^i)"
  ,"{-ar-ott2-} \\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v (j1 j2 : Interval) (xy : Eq_j ((x:A j1 j)->B x) (u j1) (v j1)). \
     \\\{x1 : A j2 0} {x2 : A j2 1} (x12 : Eq_j (A j2 j) (cast_i (A i 0) j2 j2 x1) (cast_i (A i 1) j2 j2 x2)) -> \
       \ refl_i (xy^i (cast_i (Eq_j (A i j) (cast_i (A i 0) j2 i x1) (cast_i (A i 1) j2 i x2)) j2 j1 x12)^i)"
  ,"{-ar-ott3-} \\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v (j1 j2 : Interval) (xy : Eq_j ((x:A j1 j)->B x) (u j1) (v j1)). \
     \\\{x1 : A j2 0} {x2 : A j2 1} (x12 : Eq_j (A j2 j) (cast_i (A i 0) j2 j2 x1) (cast_i (A i 1) j2 j2 x2)) -> \
     \ cast_k (Eq_j \
     \    (B {k} {j} \
     \       (iv (cast_i (A i 0) j2 k x1) (cast_i (A i 1) j2 k x2) \
     \          (cast_i (Eq_j (A i j) (cast_i (A i 0) j2 i x1) (cast_i (A i 1) j2 i x2)) j2 k x12) \
     \          j)) \
     \    (u k (cast_i (A i 0) j2 k x1)) \
     \    (v k (cast_i (A i 1) j2 k x2))) \
     \ j1 j2 \
     \ (refl_j (xy^j (cast_i (Eq_j (A i j) (cast_i (A i 0) j2 i x1) (cast_i (A i 1) j2 i x2)) j2 j1 x12)^j))"
  ,"{-ar-ott4-} \\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v (j1 j2 : Interval) (xy : Eq_j ((x:A j1 j)->B x) (u j1) (v j1)). \
     \ refl_0 (\\x -> \
     \ ((\\{x1 : A j2 0} {x2 : A j2 1} (x12 : Eq_j (A j2 j) (cast_i (A i 0) j2 j2 x1) (cast_i (A i 1) j2 j2 x2)) -> \
     \ cast_k (Eq_j \
     \    (B {k} {j} \
     \       (iv (cast_i (A i 0) j2 k x1) (cast_i (A i 1) j2 k x2) \
     \          (cast_i (Eq_j (A i j) (cast_i (A i 0) j2 i x1) (cast_i (A i 1) j2 i x2)) j2 k x12) \
     \          j)) \
     \    (u k (cast_i (A i 0) j2 k x1)) \
     \    (v k (cast_i (A i 1) j2 k x2))) \
     \ j1 j2 \
     \ (refl_j (xy^j (cast_i (Eq_j (A i j) (cast_i (A i 0) j2 i x1) (cast_i (A i 1) j2 i x2)) j2 j1 x12)^j))) \
     \ {cast_k (A j2 k) 0 0 x} {cast_k (A j2 k) 0 1 x} (refl_j (cast_k (A j2 k) 0 j x)))^0) "
  ,"{-ar-ott5-} \\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v (j1 j2 : Interval) (xy : Eq_j ((x:A j1 j)->B x) (u j1) (v j1)). \
     \ refl_j0 (\\x -> \
     \ (cast_k (Eq_j \
     \    (B {k} {j} \
     \       (iv                       (cast_i (A i 0) j2 k (cast_k (A j2 k) j0 0 x)) \
     \                                 (cast_i (A i 1) j2 k (cast_k (A j2 k) j0 1 x)) \
     \           (cast_i (Eq_j (A i j) (cast_i (A i 0) j2 i (cast_k (A j2 k) j0 0 x)) \
     \                                 (cast_i (A i 1) j2 i (cast_k (A j2 k) j0 1 x))) j2 k \
     \                   (refl_j (cast_k (A j2 k) j0 j x))) \
     \          j)) \
     \    (u k (cast_i (A i 0) j2 k (cast_k (A j2 k) j0 0 x))) \
     \    (v k (cast_i (A i 1) j2 k (cast_k (A j2 k) j0 1 x)))) \
     \ j1 j2 \
     \ (refl_j (xy^j (cast_i (Eq_j (A i j) (cast_i (A i 0) j2 i (cast_k (A j2 k) j0 0 x)) \
     \                                     (cast_i (A i 1) j2 i (cast_k (A j2 k) j0 1 x))) j2 j1 \
     \                       (refl_j (cast_k (A j2 k) j0 j x)) )^j)) \
     \ )^j0) "
  ,"{-ar-ott6-} \\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v (j1 j2 : Interval) (xy : Eq_j ((x:A j1 j)->B x) (u j1) (v j1)). \
     \ refl_j0 (\\x -> xy^j0 (cast_i (A i j0) j2 j1 x)),\
     \ refl_j0 (\\x -> xy^j0 (cast_i (Eq_j (A i j) (cast_i (A i 0) j2 i (cast_k (A j2 k) j0 0 x)) \
     \                                             (cast_i (A i 1) j2 i (cast_k (A j2 k) j0 1 x))) j2 j1 \
     \                               (refl_j (cast_k (A j2 k) j0 j x)) )^j0)"
     -}
  ,"{-ar-eq2-}\\(A : _ -> _ -> Set) (B : _ -> _ -> Set) u v j1 j2 (f : Eq_j (A j1 j -> B j1 j) (u j1) (v j1)). \
     \ refl_j (\\(x : A j2 j) -> \
     \    (cast_i (Eq_j' (B i j') (u i (cast_i (A i 0) j2 i (cast_j (A j2 j) j 0 x))) \
     \                            (v i (cast_i (A i 1) j2 i (cast_j (A j2 j) j 1 x))) ) j1 j2\
     \    (refl_j' (f^j' (cast_i (A i j') j2 j1 (cast_j (A j2 j) j j' x))))) ^j )"
  ,"{-ar-deq-}\\(A : _ -> _ -> Set) (B : ∀ {i j}. A i j -> Set) u v j1 j2 (f : Eq_j ((x:A j1 j)->B x) (u j1) (v j1)). \
     \ refl_j (\\(x : A j2 j) -> \
     \    (cast_i (Eq_j' (B {i} {j'} (cast_i (A i j') j2 i (cast_j (A j2 j) j j' x))) \
     \                      (u i (cast_i (A i 0) j2 i (cast_j (A j2 j) j 0 x))) \
     \                      (v i (cast_i (A i 1) j2 i (cast_j (A j2 j) j 1 x))) ) j1 j2\
     \    (refl_j' (f^j' (cast_i (A i j') j2 j1 (cast_j (A j2 j) j j' x))))) ^j )"
  ,"{-cast-eq-eq-pair-} \\(A B : _ -> _ -> _ -> Set) \
     \                 (u : forall i j. (A i j 0 * B i j 0)) \
     \                 (v : forall i j. (A i j 1 * B i j 1)) \
     \                 (p : (i:_) -> Eq_k (A i 0 k * B i 0 k) (u i 0) (v i 0)) \
     \                 (q : (i:_) -> Eq_k (A i 1 k * B i 1 k) (u i 1) (v i 1)) j1 j2 \
     \                 (xy : Eq_j (Eq_k (A j1 j k * B j1 j k) (u j1 j) (v j1 j)) (p j1) (q j1)). \
     \ (refl_j (refl_k ((cast_i (Eq_j (Eq_k (A i j k) (proj1 (u i j)) (proj1 (v i j))) \
     \                                (refl_k (proj1 (p i)^k)) (refl_k (proj1 (q i)^k))) j1 j2 \
     \                          (refl_j (refl_k (proj1 (xy^j)^k))))^j^k \
     \                 ,(cast_i (Eq_j (Eq_k (B i j k) (proj2 (u i j)) (proj2 (v i j))) \
     \                                (refl_k (proj2 (p i)^k)) (refl_k (proj2 (q i)^k))) j1 j2 \
     \                          (refl_j (refl_k (proj2 (xy^j)^k))))^j^k)) \
     \ : Eq_j (Eq_k (A j2 j k * B j2 j k) (u j2 j) (v j2 j)) (p j2) (q j2) )"
  ,"{-cast-eq-eq-fun-} \\(A B : _ -> _ -> _ -> Set) \
     \                 (u : forall i j. (A i j 0 -> B i j 0)) \
     \                 (v : forall i j. (A i j 1 -> B i j 1)) \
     \                 (p : (i:_) -> Eq_k (A i 0 k -> B i 0 k) (u i 0) (v i 0)) \
     \                 (q : (i:_) -> Eq_k (A i 1 k -> B i 1 k) (u i 1) (v i 1)) j1 j2 \
     \                 (f : Eq_j (Eq_k (A j1 j k -> B j1 j k) (u j1 j) (v j1 j)) (p j1) (q j1)). \
     \ refl_j (refl_k (\\(x : A j2 j k) -> \
     \    (cast_i (Eq_j' (Eq_k' (B i j' k') \
     \                            (u i j' (cast_i (A i j' 0) j2 i (cast_j (A j2 j 0) j j' (cast_k (A j2 j k) k 0 x)))) \
     \                            (v i j' (cast_i (A i j' 1) j2 i (cast_j (A j2 j 1) j j' (cast_k (A j2 j k) k 1 x)))) ) \
     \                     (refl_k' ((p i)^k' (cast_i (A i 0 k') j2 i (cast_j (A j2 j k') j 0 (cast_k (A j2 j k) k k' x))))) \
     \                     (refl_k' ((q i)^k' (cast_i (A i 1 k') j2 i (cast_j (A j2 j k') j 1 (cast_k (A j2 j k) k k' x))))) ) j1 j2 \
     \    (refl_j' (refl_k' (f^j'^k' (cast_i (A i j' k') j2 j1 (cast_j (A j2 j k') j j' (cast_k (A j2 j k) k k' x))))))  )^j^k ))"
  ]
  {-
  cast A (proj1 x) becomes (cast (Eq A) (refl_i (proj1 x)))^i
  cast A x becomes cast (Eq A) (refl_i x^i)
  From (x : A i) You can go to (refl_i' (cast_i (A i) i' i x) : Eq_i A (cast_i A i 0 x) (cast_i A i 1 x))
  -- can you do a two step thing?
  -}

-- expressions that shouldn't typecheck
badExpressions :: [String]
badExpressions =
  ["Set : Set"
  ,"f (f x)"
  ,"notInScope"
  ,"\\x. x"
  ,"(refl f) x"
  ,"f (refl x)"
  ,"data{zero:Unit; zero:Nat}"
  ,"_"
  ]

--------------------------------------------------------------------------------
-- Simple test framework
--------------------------------------------------------------------------------

showError :: Show err => Either err a -> Either String a
showError = either (Left . show) Right

testPart :: String -> Either String a -> Either String a
testPart part = either (Left . (part ++) . ("\n" ++)) Right

type MyAssertion = Either String ()

assert :: String -> Bool -> MyAssertion
assert msg False = Left $ msg
assert _   True = return ()

assertEqual :: (Eq a, Show a) => String -> a -> a -> MyAssertion
assertEqual msg x y = assert (unlines [msg,"  "++show x,"Not equal to","  "++show y]) (x == y)

assertFailed :: Show a => String -> Either err a -> MyAssertion
assertFailed _   (Left _) = Right ()
assertFailed msg (Right a) = Left (msg ++ "\n" ++ show a)

newtype TestCase = TestCase (Either String String)
  deriving Typeable

testCase :: TestName -> MyAssertion -> TestTree
testCase name = testCaseInfo name . ("" <$)

testCaseInfo :: TestName -> Either String String -> TestTree
testCaseInfo name = singleTest name . TestCase

instance IsTest TestCase where
  testOptions = return []
  run _ (TestCase (Left e))     _ = return $ testFailed e
  run _ (TestCase (Right info)) _ = return $ testPassed info

--------------------------------------------------------------------------------
-- Test of parser and typechecker
--------------------------------------------------------------------------------

testTcM :: EvalAllMetas a => TcM a -> a
testTcM x = case runTcM testCtx (x >>= evalAllMetasThrow) of
  Left e -> error (show e)
  Right y -> y

testTcM' :: EvalAllMetas a => TcM a -> (a,Doc)
testTcM' x = testTcM ((,) <$> x <*> dumpMetas)

myTestTcM :: (EvalAllMetas a, Pretty TcM a) => TcM a -> Either String a
myTestTcM mx = showError $ runTcM testCtx $ do
  x <- mx
  evalAllMetasThrow x `annError` (text "in" <+> tcPpr 0 x)

testExp :: String -> Either String String
testExp xStr = do
  -- we should be able to parse the expression
  x <- testPart "Parsing" $
    showError $ runParser parseExpTop "input" xStr
  -- we should be able to pretty print and re-parse
  testPart "Pretty printer" $ do
    let xStr' = show x
    x' <- showError $ runParser parseExpTop "prety-printed" xStr'
    assertEqual "parse.ppr not identity" x x'
  -- we should be able to infer its type
  (x',ty) <- testPart "Type inference" $
    myTestTcM $ tc Nothing x
  {--- we should still be able to pretty print and re-parse, after type inference
  -- but this doesn't hold because we don't pretty print the type information in SumElim.
  testPart "Pretty printer(typechecked)" $ do
    x'' <- showError $ runParser parseExpTop "prety-printed" (show x')
    assertEqual "parse.ppr not identity" x' x''-}
  -- and the modified expression should yield the same type
  testPart "Type inference of expanded expression" $ do
    (x'',ty') <- myTestTcM $ tc Nothing x'
    tyNf <- myTestTcM $ tcEval NF ty
    ty'Nf <- myTestTcM $ tcEval NF ty'
    assertEqual "Values should be equal" x' x''
    assertEqual "Types should be equal" tyNf ty'Nf
  -- and we should also be able to typecheck it
  testPart "Type checking" $ do
    xty' <- myTestTcM $ tc (Just ty) x'
    assertEqual "Should be equal" (x',ty) xty'
  -- evaluation (to normal form) should preserve typing
  xnf <- testPart "Evaluation preserves typing" $ do
    xnf <- myTestTcM $ tcEval NF x'
    (_,ty') <- myTestTcM $ tc (Just ty) xnf
      `annError` text "Original expression: " $/$ (tcPpr 0 x')
              $$ text "Normal form expression: " $/$ (tcPpr 0 xnf)
    -- ty and ty' should have the same normal form (we already know that they unify)
    tyNf <- myTestTcM $ tcEval NF ty
    ty'Nf <- myTestTcM $ tcEval NF ty'
    assertEqual "Should have same type in normal form" tyNf ty'Nf
    return xnf
  -- eval NF should also give a normal form
  testPart "Normal form" $ do
    xnf' <- myTestTcM $ tcEval NF xnf
    assertEqual "eval NF should give normal form" xnf xnf'
  -- all the ways to evaluate x to normal form should give the same result
  testPart "Evaluation" $ do
    return ()
  -- return some info
  --return ""
  tyNf <- myTestTcM $ tcEval NF ty
  return $ show tyNf

testBadExp :: String -> Either String ()
testBadExp xStr = do
  x <- testPart "Parsing" $
    showError $ runParser parseExpTop "input" xStr
  assertFailed "Type inference should fail" $
    myTestTcM $ tc Nothing x

--------------------------------------------------------------------------------
-- repl utilities
--------------------------------------------------------------------------------

-- search for a goodExpression
findExp :: String -> String
findExp query = case filter (("{-"++query) `isPrefixOf`) goodExpressions of
  [x] -> x
  []  -> error $ "Query not found: " ++ query
  _   -> error $ "Multiple results for: " ++ query

testExp' :: String -> IO ()
testExp' x = do
  putStrLn $ take 40 x
  putStrLn $ either ("FAIL\n"++) ("OK\n"++) $ testExp x

--------------------------------------------------------------------------------
-- Main: testcases
--------------------------------------------------------------------------------

-- 
--splitTest :: 

tests :: TestTree
tests = testGroup "Tests"
  [ testGroup "Should pass"
    [ testCaseInfo (show i ++ " " ++ take 25 xStr) (testExp xStr) | (i,xStr) <- zip [0..] goodExpressions ]
  , testGroup "Should fail"
    [ testCase (show i ++ " " ++ take 20 xStr) (testBadExp xStr) | (i,xStr) <- zip [0..] badExpressions ]
  ]

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  defaultMain tests

