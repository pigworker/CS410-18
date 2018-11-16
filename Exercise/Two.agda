{-# OPTIONS --type-in-type #-}

module Exercise.Two where

open import Lib.Basics
open import Lib.Indexed       -- important stuff in here!
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.NatTrans
open import Lib.Cat.Monad
open import Lib.Cat.Adjunction

open import Exercise.One

------------------------------------------------------------------------------
-- CATEGORIES OF INDEXED OBJECTS AND ARROWS
------------------------------------------------------------------------------

-- We fix an underlying category and a set I for "index"...

module _ {Obj : Set}{Arr : Obj -> Obj -> Set}(I : Set)(C : Category Arr) where

  open Category C

  -- ... and now your job is to build a new category whose
  -- objects are I-indexed families of underlying objects, and whose
  -- arrows are index-respecting families of underlying arrows

  _-C>_ : Category {I -> Obj} \ S T -> (i : I) -> Arr (S i) (T i)
  _-C>_ = {!!}


-- Now we give you a function f : I -> J between two index sets.

module _ {Obj : Set}{Arr : Obj -> Obj -> Set}{I J : Set}
       (f : I -> J)(C : Category Arr) where

  open Category C
  open Functor

  -- Show that you get a functor from J-indexed things to I-indexed things.

  Reindex : Functor (J -C> C) (I -C> C) (f -_)
  Reindex = {!!}


------------------------------------------------------------------------------
-- FUNCTORIALITY OF ALL
------------------------------------------------------------------------------

-- We have All in the library. Show that it is a functor from
-- element-indexed sets to list-indexed sets.

module _ where

  open Functor

  all : {I : Set}{P Q : I -> Set} ->
        [ P -:> Q ] ->
        [ All P -:> All Q ]
  all f is ps = {!!}

  ALL : (I : Set) -> Functor (I -C> SET) (List I -C> SET) All
  ALL I = {!!}


------------------------------------------------------------------------------
-- ALL BY TABULATION
------------------------------------------------------------------------------

-- The list membership relation is given by thinning from singletons.

_<-_ : {I : Set} -> I -> List I -> Set
i <- is = (i ,- []) <: is

-- If every element of a list satisfies P, you should be able to
-- collect all the Ps.

tabulate : {I : Set}{P : I -> Set}(is : List I) ->
             [ (_<- is) -:> P ] -> All P is
tabulate is f = {!!}

module _ (I : Set) where  -- fix an element set and open handy kit
  open Category (I -C> SET)
  open Functor
  open NaturalTransformation

  -- Show that the functional presentation of "each element is P"
  -- also gives you a functor.

  AllMem : Functor (I -C> SET) (List I -C> SET) \ P is -> [ (_<- is) -:> P ]
  AllMem = {!!}

  -- Prove that tabulate is natural.

  tabulateNT : NaturalTransformation AllMem (ALL I)
  transform tabulateNT _ = tabulate
  natural tabulateNT = {!!}

