{-# OPTIONS --type-in-type --no-unicode #-}
{-# OPTIONS --allow-unsolved-metas #-}
module Lib.Cat.ArrowFunctor where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.ProductCat
open import Lib.Cat.Solver


ARROWS : {Obj : Set}{Arr : Obj -> Obj -> Set}(C : Category Arr) ->
         Functor ((C ^op)  *Cat C) SET \ { (X , Y) -> Arr X Y }
Functor.map (ARROWS C) {A = (X , X')} {B = (Y , Y')} (f , g) h = f -arr- h -arr- g where open Category C
Functor.mapidArr (ARROWS C) = ext \ h ->
  [=IN C !
   idSyn -syn- < h > -syn- idSyn
     =[[ categories refl >>=
   < h >
     [[QED]]
   =]
Functor.map-arr- (ARROWS C) (f , f') (g , g') = ext \ h ->
  [=IN C !
    (< g > -syn- < f >) -syn- (< h > -syn- < f' > -syn- < g' >)
      =[[ categories refl >>=
    < g > -syn- (< f > -syn- < h > -syn- < f' >) -syn- < g' >
      [[QED]]
  =]


{-

[=IN C !
  idSyn -syn- (< h >  -syn- idSyn)
    =[[ categories refl >>=
  < h >
    [[QED]]
  =]
-}
