{-# OPTIONS --type-in-type --no-unicode #-}
module Lib.Cat.Adjunction where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.NatTrans
open import Lib.Cat.ProductCat
open import Lib.Cat.ArrowFunctor

record Adjunction
  {ObjC : Set}{ArrC : ObjC -> ObjC -> Set}{CatC : Category ArrC}
  {ObjD : Set}{ArrD : ObjD -> ObjD -> Set}{CatD : Category ArrD}
  {ObjF : ObjC -> ObjD}(F : Functor CatC CatD ObjF)
  {ObjG : ObjD -> ObjC}(G : Functor CatD CatC ObjG)
  : Set where
  open Functor
  open NaturalTransformation
  field
    down : NaturalTransformation
             (((F ^opFun) *Fun (ID CatD)) -Func- (ARROWS CatD))
             ((((ID CatC) ^opFun) *Fun G) -Func- (ARROWS CatC))
    up   : NaturalTransformation
             ((((ID CatC) ^opFun) *Fun G) -Func- (ARROWS CatC))
             (((F ^opFun) *Fun (ID CatD)) -Func- (ARROWS CatD))
    updown : {X : ObjC}{B : ObjD}{h : ArrC X (ObjG B)} ->
             transform down _ (transform up _ h) == h
    downup : {A : ObjC}{Y : ObjD}{h' : ArrD (ObjF A) Y} ->
             transform up _ (transform down _ h') == h'

--    forall X : ObjC, B : ObjD.
--
--            F X  -->   B
--            ============
--              X  --> G B

-- Notation: F ⊣ G, "F is left adjoint to G" or eq. "G is right adjoint to F"
