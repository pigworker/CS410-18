{-# OPTIONS --type-in-type --no-unicode #-}
module Lecture.Six where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.NatTrans
open import Lib.Cat.Adjunction
open import Lib.Cat.Monad

{-
module _ {ObjF : Set -> Set}(F : Functor SET SET ObjF) where

  open NaturalTransformation
  open MonadMorphism
  open Functor
  open Monad

  data M (X : Set) : Set where
    ret : X -> M X
    layer : ObjF (M X) -> M X

-- ObjF X = X -> X would make Agda allow programs that loop

-- ObjF X = (X -> Two) -> Two is a functor, but allowing this makes
--   the logic inconsistent with classical logic: it claims Pow (PowX) = X

  funM : Functor SET SET M
  map funM h (ret x) = ret (h x)
  map funM h (layer fx) = layer {!!}
  mapidArr funM = {!!}
  map-arr- funM = {!!}

  retM : NaturalTransformation (ID SET) funM
  transform retM X = ret
  natural retM = {!!}

  joinM : NaturalTransformation (funM -Func- funM) funM
  transform joinM X (ret mx) = mx
  transform joinM X (layer fx) = layer {!!}
  natural joinM = {!!}

  MonadM : Monad funM
  returnNT MonadM = retM
  joinNT MonadM = joinM
  returnJoin MonadM = {!!}
  mapReturnJoin MonadM = {!!}
  joinJoin MonadM = {!!}
 
  morph : {ObjN : Set -> Set}{N : Functor SET SET ObjN}(MonadN : Monad N)
          (f : NaturalTransformation F N) ->
          MonadMorphism MonadM MonadN
  transform (mMorph (morph MonadN f)) X (ret x) = transform (returnNT MonadN) X x
  transform (mMorph (morph MonadN f)) X (layer fx) = {!!}
  natural (mMorph (morph MonadN f)) k = {!!}
  mMorphReturn (morph MonadN f) X = refl
  mMorphJoin (morph MonadN f) = {!!}
-}

record Con{-tainer-} : Set where
  constructor _<!_
  field
    Sh{-ape-} : Set
    Po{-sition-} : Sh -> Set

[[_]]C : Con -> Set -> Set
[[ Sh <! Po ]]C X = Sg Sh \ s -> Po s -> X

[[_]]CF : (C : Con) -> Functor SET SET [[ C ]]C
Functor.map [[ C ]]CF f (s , g) = s , (g - f)
Functor.mapidArr [[ C ]]CF = refl
Functor.map-arr- [[ C ]]CF k l = refl

data M (C : Con)(X : Set) : Set where
  ret : X -> M C X
  layer : [[ C ]]C (M C X) -> M C X

join : {C : Con}{X : Set} -> M C (M C X) -> M C X
join (ret mx) = mx
join (layer (s , f)) = layer (s , (\ p -> join (f p)))
