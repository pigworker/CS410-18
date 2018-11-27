{-# OPTIONS --type-in-type --no-unicode #-}
--{-# OPTIONS --irrelevant-projections #-}
module Lib.Cat.ProductCat where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor

_*Cat_ : {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}(CatS : Category ArrS)
         {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}(CatT : Category ArrT) ->
         Category {ObjS * ObjT} \ {(SS , TS) (ST , TT) ->
           ArrS SS ST * ArrT TS TT}
CatS *Cat CatT =
  record
    { idArr = (S.idArr , T.idArr)
    ; _-arr-_ = \ { (fS , fT) (gS , gT) -> (fS S.-arr- gS) , (fT T.-arr- gT) }
    ; idArr-arr- = \ { {AS , AT} {BS , BT} (fS , fT) ->
                          reff _,_ =$= (Category.idArr-arr- CatS fS) =$= (Category.idArr-arr- CatT fT) }
    ; _-arr-idArr = \ { {AS , AT} {BS , BT} (fS , fT) ->
                          reff _,_ =$= (Category._-arr-idArr CatS fS) =$= (Category._-arr-idArr CatT fT) }
    ; assoc-arr- = \ { (fS , fT) (gS , gT) (hS , hT) -> reff _,_ =$= Category.assoc-arr- CatS fS gS hS =$= Category.assoc-arr- CatT fT gT hT }
    }
  where
    module S = Category CatS
    module T = Category CatT

module _
         {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
         {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
         {ObjF : ObjS -> ObjT}(F : Functor CatS CatT ObjF)
         {ObjS' : Set}{ArrS' : ObjS' -> ObjS' -> Set}{CatS' : Category ArrS'}
         {ObjT' : Set}{ArrT' : ObjT' -> ObjT' -> Set}{CatT' : Category ArrT'}
         {ObjF' : ObjS' -> ObjT'}(F' : Functor CatS' CatT' ObjF')
  where
    private
      module F = Functor F
      module F' = Functor F'
      open Functor

    _*Fun_ :
         Functor (CatS *Cat CatS') (CatT *Cat CatT')
           \ { (S , S') -> (ObjF S , ObjF' S') }
    map _*Fun_ (f , f') = (F.map f) , (F'.map f')
    mapidArr _*Fun_ = reff _,_ =$= F.mapidArr =$= F'.mapidArr
    map-arr- _*Fun_ (f , f') (g , g') =
      reff _,_ =$= F.map-arr- f g =$= F'.map-arr- f' g'
