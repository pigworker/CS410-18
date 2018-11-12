{-# OPTIONS --type-in-type --no-unicode #-}
module Lib.Cat.NatTrans where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.Solver

record NaturalTransformation
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
  {ObjF : ObjS -> ObjT}(F : Functor CatS CatT ObjF)
  {ObjG : ObjS -> ObjT}(G : Functor CatS CatT ObjG)
  : Set where
  open Category CatT
  open Functor
  field
    transform : (X : ObjS) -> ArrT (ObjF X) (ObjG X)
    .natural : {X Y : ObjS} -> (f : ArrS X Y) ->
               (transform X -arr- map G f) == (map F f -arr- transform Y)


module _
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
  where

  open Category CatT
  open Functor
  open NaturalTransformation

  idNT : {ObjF : ObjS -> ObjT}{F : Functor CatS CatT ObjF} ->
         NaturalTransformation F F
  transform (idNT {ObjF} {F}) X = idArr
  natural (idNT {ObjF} {F}) f =
    [=IN CatT !
     (idSyn -syn- mapSyn F < f >) =[[ categories refl >>=
     (mapSyn F < f > -syn- idSyn)
       [[QED]]
    =]

  _-NT-_ : {ObjF ObjG ObjH : ObjS -> ObjT}
           {F : Functor CatS CatT ObjF}
           {G : Functor CatS CatT ObjG}
           {H : Functor CatS CatT ObjH}
           (fg : NaturalTransformation F G)
           (gh : NaturalTransformation G H)
           ->    NaturalTransformation F H
  transform (fg -NT- gh) X = transform fg X -arr- transform gh X
  natural (_-NT-_ {F = F} {G} {H} fg gh) {X} {Y} f =
    [=IN CatT !
      ((< transform fg X > -syn- < transform gh X >) -syn- mapSyn H < f >)
        =[[ categories refl >>=
      (< transform fg X > -syn- -[ < transform gh X > -syn- mapSyn H < f > ]-)
        =[[ reduced (rd , rq (natural gh f)) >>=
      (< transform fg X > -syn- -[ mapSyn G < f > -syn- < transform gh Y > ]-)
        =[[ categories refl >>=
      (-[ < transform fg X > -syn- mapSyn G < f > ]- -syn- < transform gh Y >)
        =[[ reduced (rq (natural fg f) , rd) >>=
      (-[ mapSyn F < f > -syn- < transform fg Y > ]- -syn- < transform gh Y >)
        =[[ categories refl >>=
      (mapSyn F < f > -syn- < transform fg Y > -syn- < transform gh Y >)
        [[QED]]
    =]


  module _ {ObjF ObjG : ObjS -> ObjT}
           {F : Functor CatS CatT ObjF}{G : Functor CatS CatT ObjG}
           where

   eqNatTrans :
     (p q : NaturalTransformation F G) ->
     ((X : ObjS) -> transform p X == transform q X) ->         
     p == q
   eqNatTrans (record { transform = pt ; natural = _ })
              (record { transform = qt ; natural = _ })
              prf
     rewrite ext prf = refl


module _
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}(CatS : Category ArrS)
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}(CatT : Category ArrT)
  where

  open Category CatT

  FUNCTOR : Category {SomeFunctor (ObjS , ArrS , CatS) (ObjT , ArrT , CatT)}
             \ {(ObjF , F) (ObjG , G) -> NaturalTransformation F G }
  idArr FUNCTOR = idNT
  _-arr-_ FUNCTOR fg gh = fg -NT- gh
  idArr-arr- FUNCTOR f = eqNatTrans _ _ \ X -> idArr-arr- _
  _-arr-idArr FUNCTOR f = eqNatTrans _ _ \ X -> _ -arr-idArr
  assoc-arr- FUNCTOR f g h = eqNatTrans _ _ \ X -> assoc-arr- _ _ _
