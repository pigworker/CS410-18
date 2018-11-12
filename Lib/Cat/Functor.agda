{-# OPTIONS --type-in-type --no-unicode #-}
{- OPTIONS --irrelevant-projections -}
module Lib.Cat.Functor where

open import Lib.Basics
open import Lib.Cat.Category

record Functor
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}(CatS : Category ArrS)
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}(CatT : Category ArrT)
  (ObjF : ObjS -> ObjT)
  : Set where
  private module S = Category CatS
  private module T = Category CatT
  field
    map      : forall {A B : ObjS} -> ArrS A B -> ArrT (ObjF A) (ObjF B)
    -- laws
    .mapidArr : forall {A} -> map (S.idArr {A}) == T.idArr {ObjF A}
    .map-arr- : forall {A B C}(f : ArrS A B)(g : ArrS B C) ->
                map (f S.-arr- g) == (map f T.-arr- map g)

SomeFunctor : SomeCategory -> SomeCategory -> Set
SomeFunctor (ObjS , ArrS , CatS) (ObjT , ArrT , CatT) =
   Sg (ObjS -> ObjT) \ ObjF ->
   Functor CatS CatT ObjF

ID : {Obj : Set}{Arr : Obj -> Obj -> Set}(C : Category Arr) -> Functor C C \ X -> X
ID C = record { map = id ; mapidArr = refl ; map-arr- = \ f g -> refl }

module _
  {ObjR : Set}{ArrR : ObjR -> ObjR -> Set}{CatR : Category ArrR}
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
  {ObjF : ObjR -> ObjS}
  {ObjG : ObjS -> ObjT}
  where
  private
    module R = Category CatR
    module S = Category CatS
    module T = Category CatT

  _-Func-_ :  Functor CatR CatS ObjF
           ->
              Functor CatS CatT ObjG
           ->
              Functor CatR CatT (ObjF - ObjG)
  Functor.map (F -Func- G) = F.map - G.map
    where
    module F = Functor F
    module G = Functor G
  Functor.mapidArr (F -Func- G) =
      G.map (F.map R.idArr)
        =[ G.map $= F.mapidArr >=
      G.map S.idArr
        =[ G.mapidArr >=
      T.idArr
        [QED]
    where
    module F = Functor F
    module G = Functor G
  Functor.map-arr- (F -Func- G) f g =
      G.map (F.map (f R.-arr- g))
        =[ G.map $= F.map-arr- f g >=
      G.map (F.map f S.-arr- F.map g)
        =[ G.map-arr- (F.map f) (F.map g) >=
      (G.map (F.map f) T.-arr- G.map (F.map g))
        [QED]
    where
    module F = Functor F
    module G = Functor G

  infixr 20 _-Func-_

CATEGORY : Category SomeFunctor
CATEGORY = record
             { idArr = _ , ID _
             ; _-arr-_ = \ { (ObjF , F) (ObjG , G) -> _ , (F -Func- G) }
             ; idArr-arr- = \ F -> refl
             ; _-arr-idArr = \ F -> refl
             ; assoc-arr- = \ F G H -> refl
             }

open Functor

_^opFun : {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
          {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
          {ObjF : ObjS -> ObjT} ->
          Functor CatS CatT ObjF -> Functor (CatS ^op) (CatT ^op) ObjF
map (F ^opFun) = map F
mapidArr (F ^opFun) = mapidArr F
map-arr- (F ^opFun) f g = map-arr- F g f
