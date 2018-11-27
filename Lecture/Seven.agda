{-# OPTIONS --type-in-type --no-unicode #-}
module Lecture.Seven where

open import Lib.Basics
open import Lib.Nat

open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.NatTrans

open import Lecture.Six

{-
record Con{-tainer-} : Set where
  constructor _<!_
  field
    Sh{-ape-} : Set
    Po{-sition-} : Sh -> Set

[[_]]C : Con -> Set -> Set
[[ Sh <! Po ]]C X = Sg Sh \ s -> Po s -> X

map<! : {C : Con} -> {X Y : Set} -> (X -> Y) -> [[ C ]]C X -> [[ C ]]C Y
map<! f (s , g) = (s , (g - f))

[[_]]CF : (C : Con) -> Functor SET SET [[ C ]]C
map [[ C ]]CF = map<!
mapidArr [[ C ]]CF = refl
map-arr- [[ C ]]CF k l = refl
-}

-- NEXT: Container morphisms

record ConMor (C C' : Con) : Set where
  constructor _<!mor_
  open Con
  field
    sh : Sh C -> Sh C'
    po : {s : Sh C} -> Po C' (sh s) -> Po C s

module _ {C C' : Con} where

  open NaturalTransformation
  open ConMor

  [[_]]NT : ConMor C C' -> NaturalTransformation [[ C ]]CF [[ C' ]]CF
  [[ f <!mor g ]]NT = {!!}

  complete : (nt : NaturalTransformation [[ C ]]CF [[ C' ]]CF) ->
             Sg (ConMor C C') (\ m -> [[ m ]]NT == nt)
  complete nt = {!!}

-- Indexed containers

-- What they mean

-- How they are functorial

-- All our favourite things are (indexed) containers

---- vectors

---- products

---- sums

-- if there's time (ha!): least fixed points
