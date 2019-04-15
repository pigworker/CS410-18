{-# OPTIONS --type-in-type --no-unicode #-}
--{-# OPTIONS --irrelevant-projections #-}
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
  open Con
  open ConMor

  [[_]]NT : ConMor C C' -> NaturalTransformation [[ C ]]CF [[ C' ]]CF
  transform [[ f <!mor g ]]NT X (s , k) = (f s) , (g - k)
  natural [[ f <!mor g ]]NT h = refl

  ntConMor : (nt : NaturalTransformation [[ C ]]CF [[ C' ]]CF) ->
             ConMor C C'
  ntConMor nt = (\ s -> fst (transform nt (Po C s) (s , id)))
          <!mor \ {s} p' -> snd (transform nt (Po C s) (s , id)) p'

  .complete : (nt : NaturalTransformation [[ C ]]CF [[ C' ]]CF) ->
              [[ ntConMor nt ]]NT == nt
  complete nt = eqNatTrans _ _ \ X -> ext \ { (s , k) -> natural nt k =$ (s , id) }


ConMorBis : (C C' : Con) -> Set
ConMorBis (S <! P) C' =  (s : S) -> [[ C' ]]C (P s)

module _ {C C' : Con} where

  open NaturalTransformation
  open Con
  open ConMor

  [[_]]NTBis : ConMorBis C C' -> NaturalTransformation [[ C ]]CF [[ C' ]]CF
  transform [[ f ]]NTBis X (s , k) with f s
  ... | s' , g = s' , (g - k)
  natural [[ f ]]NTBis h = refl

  ntConMorBis : (nt : NaturalTransformation [[ C ]]CF [[ C' ]]CF) ->
             ConMorBis C C'
  ntConMorBis nt s = transform nt (Po C s) (s , id)

  .completeBis : (nt : NaturalTransformation [[ C ]]CF [[ C' ]]CF) ->
              [[ ntConMorBis nt ]]NTBis == nt
  completeBis nt = eqNatTrans _ _ \ X ->
    ext \ { (s , k) -> natural nt k =$ (s , id) }


-- Indexed containers

module _ {O I : Set} where
  record Hancock : Set where
    constructor _<[_!_]
    field
      Command  : O -> Set
      Response : (o : O) -> Command o -> Set
      result   : (o : O)(c : Command o) -> Response o c -> I

-- What they mean

  [[_]]H : Hancock -> (I -> Set) -> (O -> Set)
  [[ Co <[ Re ! re ] ]]H P o = Sg (Co o) \ c -> (r : Re o c) -> P (re o c r)

-- How they are functorial

-- All our favourite things are (indexed) containers

---- vectors

---- products

---- sums

-- if there's time (ha!): least fixed points
