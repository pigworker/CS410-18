{-# OPTIONS --type-in-type --no-unicode #-}
module Lecture.Five where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.NatTrans
open import Lib.Cat.Adjunction

open import Lecture.Four -- the PREORDER category

open Functor
open NaturalTransformation
open Adjunction

-- finishing off Lib.Cat.Solver
-- the A-word:
--   how did we come up with what to prove about FREE R?
--   adjunctions, informally
--   the ARROWS functor
--   examples of adjunctions
--     adjoints to forgetful functors
--     curry and uncurry







open MonotoneMap

-- forgetful functor that forgets about the order

FORGETORDER : Functor PREORDER SET \ { (X , _) -> X }
map FORGETORDER = mapData
mapidArr FORGETORDER = refl
map-arr- FORGETORDER f g = refl


-- the discrete order on a set: everything is only related to itself

discreteOrder : (X : Set) -> Preorder {X = X} _==_
Preorder.reflexive (discreteOrder X) = refl
Preorder.transitive (discreteOrder X) p q = _ =[ p >= _ =[ q >= _ [QED]
Preorder.irrelevant (discreteOrder X) {p = refl} {refl} = refl

DISCRETE : Functor SET PREORDER \ X -> (X , _==_ , discreteOrder X)
map DISCRETE f = record { mapData = f ; mapMonotone = \ p -> f $= p }
mapidArr DISCRETE = refl
map-arr- DISCRETE f g = refl

-- the indiscrete ("chaotic") order on a set: everything is related everything

indiscreteOrder : (X : Set) -> Preorder {X = X} (\ _ _ -> One)
Preorder.reflexive (indiscreteOrder X) = <>
Preorder.transitive (indiscreteOrder X) = \ _ _ -> <>
Preorder.irrelevant (indiscreteOrder X) = refl

INDISCRETE : Functor SET PREORDER \ X -> (X , _ , indiscreteOrder X)
map INDISCRETE f = record { mapData = f ; mapMonotone = _ }
mapidArr INDISCRETE = refl
map-arr- INDISCRETE f g = refl

-- adjunctions

leftAdjoint : Adjunction DISCRETE FORGETORDER
transform (down leftAdjoint) (B , (P , _<=_ , prf)) = mapData
natural (down leftAdjoint) f = refl
mapData (transform (up leftAdjoint) (B , P , _<=_ , prf) g) = g
mapMonotone (transform (up leftAdjoint) (B , P , _<=_ , prf) g) refl = Preorder.reflexive prf
natural (up leftAdjoint) f = refl
updown leftAdjoint = refl
downup leftAdjoint = refl

rightAdjoint : Adjunction FORGETORDER INDISCRETE
rightAdjoint = {!!} -- homework


-- curry and uncurry

TIMES : (A : Set) -> Functor SET SET \ X -> X * A
map (TIMES A) f (x , a) = f x , a
mapidArr (TIMES A) = refl
map-arr- (TIMES A) f g = refl

_TO : (A : Set) -> Functor SET SET \ X -> (A -> X)
map (A TO) f = \ h -> h - f
mapidArr (A TO) = refl
map-arr- (A TO) f g = refl

exponential : {A : Set} -> Adjunction (TIMES A) (A TO)
transform (down (exponential {A})) (X , B) = curry
  where curry : ((X * A) -> B) -> (X -> (A -> B))
        curry f x a = f (x , a)
natural (down (exponential {A})) g = refl
transform (up (exponential {A})) (X , B) = uncurry
  where uncurry : (X -> (A -> B)) -> ((X * A) -> B)
        uncurry g (x , a) = g x a
natural (up (exponential {A})) f = refl
updown (exponential {A}) = refl
downup (exponential {A}) = refl
