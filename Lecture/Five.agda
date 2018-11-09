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
FORGETORDER = {!!}

















-- the discrete order on a set: everything is only related to itself

discreteOrder : (X : Set) -> Preorder {X = X} _==_
discreteOrder X = {!!}

DISCRETE : Functor SET PREORDER \ X -> (X , _==_ , discreteOrder X)
DISCRETE = {!!}

-- the indiscrete ("chaotic") order on a set: everything is related everything

indiscreteOrder : (X : Set) -> Preorder {X = X} (\ _ _ -> One)
indiscreteOrder X = {!!}

INDISCRETE : Functor SET PREORDER \ X -> (X , _ , indiscreteOrder X)
INDISCRETE = {!!}

-- adjunctions

leftAdjoint : Adjunction DISCRETE FORGETORDER
leftAdjoint = {!!}

rightAdjoint : Adjunction FORGETORDER INDISCRETE
rightAdjoint = {!!}


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
exponential {A} = {!!}
