{-# OPTIONS --type-in-type #-}

module Lecture.Four where

open import Lib.Basics
open import Lib.Nat
open import Lib.Vec

postulate
  ext : {S : Set}{T : S -> Set}{f g : (x : S) -> T x} ->
        ((x : S) -> f x == g x) -> f == g

record Category {Obj : Set}(Arr : Obj -> Obj -> Set) : Set where
  field
    -- structure
    idArr       : {X : Obj} -> Arr X X
    _-arr-_     : {R S T : Obj} -> Arr R S -> Arr S T -> Arr R T
    -- laws
    idArr-arr-  : {S T : Obj}(f : Arr S T) -> (idArr -arr- f) == f
    _-arr-idArr : {S T : Obj}(f : Arr S T) -> (f -arr- idArr) == f
    assoc-arr-  : {R S T U : Obj}
                  (f : Arr R S)(g : Arr S T)(h : Arr T U) ->
                  ((f -arr- g) -arr- h) == (f -arr- (g -arr- h))

SET : Category \ S T -> S -> T
SET = record
        { idArr = λ z → z
        ; _-arr-_ = λ f g → λ r → g (f r)
        ; idArr-arr- = λ f → refl
        ; _-arr-idArr = λ f → refl
        ; assoc-arr- = λ f g h → refl
        }

refl-LE : (n : Nat) -> n <= n
refl-LE zero = <>
refl-LE (suc n) = refl-LE n

trans-LE : (x y z : Nat) -> x <= y -> y <= z -> x <= z
trans-LE zero y z xy yz = <>
trans-LE (suc x) zero z () yz
trans-LE (suc x) (suc y) zero xy ()
trans-LE (suc x) (suc y) (suc z) xy yz = trans-LE x y z xy yz

irrelevant-LE : (x y : Nat) (p q : x <= y) -> p == q
irrelevant-LE zero y p q = refl
irrelevant-LE (suc x) zero p ()
irrelevant-LE (suc x) (suc y) p q = irrelevant-LE x y p q

NAT-LE : Category _<=_
NAT-LE = record
           { idArr = \ {X} -> refl-LE X
           ; _-arr-_ = \ {x}{y}{z} -> trans-LE x y z
           ; idArr-arr- = \ {x}{y} f -> irrelevant-LE x y _ _
           ; _-arr-idArr = \ {x}{y} f -> irrelevant-LE x y _ _
           ; assoc-arr- = \ {x}{y}{z}{w} f g h -> irrelevant-LE x w _ _
           }

--_^op : forall {Obj}{Arr : Obj -> Obj -> Set} ->
--       Category Arr -> Category \ S T -> Arr T S
--C ^op = {!!}
--  where open Category C

ADDITION : Category {One} \ _ _ -> Nat
ADDITION = record
             { idArr = 0
             ; _-arr-_ = _+N_
             ; idArr-arr- = \n -> refl
             ; _-arr-idArr = _+Nzero
             ; assoc-arr- = assoc+N
             }

record Preorder {X : Set}(_<?=_ : X -> X -> Set) : Set where
  field
    reflexive   : {x : X} -> x <?= x
    transitive  : {x y z : X} ->
                  x <?= y -> y <?= z -> x <?= z
    irrelevant  : {x y : X}{p q : x <?= y} -> p == q

SomePreorder : Set1
SomePreorder =
  Sg Set             \ X ->
  Sg (X -> X -> Set) \ _<?=_ ->
  Preorder _<?=_

record MonotoneMap (XP YP : SomePreorder) : Set where
  field
    mapData     : fst XP -> fst YP
    mapMonotone :
      let X , _<X=_ , _ = XP
          Y , _<Y=_ , _ = YP
      in  {x0 x1 : X} -> x0 <X= x1 ->
                 mapData x0 <Y= mapData x1

--PREORDER : Category MonotoneMap
--PREORDER = {!!}

record Functor
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}(CatS : Category ArrS)
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}(CatT : Category ArrT)
  (ObjF : ObjS -> ObjT)
  : Set where
  module S = Category CatS
  module T = Category CatT
  field
    map      : forall {A B : ObjS} -> ArrS A B -> ArrT (ObjF A) (ObjF B)
    -- laws
    mapidArr : forall {A} -> map (S.idArr {A}) == T.idArr {ObjF A}
    map-arr- : forall {A B C}(f : ArrS A B)(g : ArrS B C) ->
               map (f S.-arr- g) == (map f T.-arr- map g)

--LIST : Functor SET SET List
--LIST = {!!}

--VEC : (n : Nat) -> Functor SET SET (\ X -> Vec X n)
--VEC n = {!!}

--TAKE : (X : Set) -> Functor (NAT-LE ^op) SET (Vec X)
--TAKE X = {!!}

record NaturalTransformation
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
  (ObjF : ObjS -> ObjT)(F : Functor CatS CatT ObjF)
  (ObjG : ObjS -> ObjT)(G : Functor CatS CatT ObjG)
  : Set where
  constructor natTrans
  open Category CatT
  open Functor
  field
    transform : (X : ObjS) -> ArrT (ObjF X) (ObjG X)
    natural : {X Y : ObjS} -> (f : ArrS X Y) ->
              (transform X -arr- map G f) == (map F f -arr- transform Y)
