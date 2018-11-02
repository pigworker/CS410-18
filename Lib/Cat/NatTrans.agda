{-# OPTIONS --type-in-type --no-unicode #-}
module Lib.Cat.NatTrans where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor

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
