{-# OPTIONS --type-in-type --no-unicode #-}
module Lib.Cat.Category where

open import Lib.Basics

postulate
  ext : {S : Set}{T : S -> Set}{f g : (x : S) -> T x} ->
        ((x : S) -> f x == g x) -> f == g

record Category {Obj : Set}(Arr : Obj -> Obj -> Set) : Set where
  field
    -- structure
    idArr       : {X : Obj} -> Arr X X
    _-arr-_     : {R S T : Obj} -> Arr R S -> Arr S T -> Arr R T
    -- laws
    .idArr-arr-  : {S T : Obj}(f : Arr S T) -> (idArr -arr- f) == f
    ._-arr-idArr : {S T : Obj}(f : Arr S T) -> (f -arr- idArr) == f
    .assoc-arr-  : {R S T U : Obj}
                   (f : Arr R S)(g : Arr S T)(h : Arr T U) ->
                   ((f -arr- g) -arr- h) == (f -arr- (g -arr- h))
  infixr 20 _-arr-_

SomeCategory : Set
SomeCategory = Sg Set                 \ Obj ->
               Sg (Obj -> Obj -> Set) \ Arr ->
               Category Arr

_^op : forall {Obj}{Arr : Obj -> Obj -> Set} ->
       Category Arr -> Category \ S T -> Arr T S
C ^op = record
          { idArr = idArr
          ; _-arr-_ = \ g f -> f -arr- g
          ; idArr-arr- = \ f -> f -arr-idArr
          ; _-arr-idArr = \ f -> idArr-arr- f
          ; assoc-arr- = \ f g h -> sym (assoc-arr- h g f)
          }
  where open Category C

SET : Category \ S T -> S -> T
SET = record
        { idArr = id
        ; _-arr-_ = \ f g -> f - g
        ; idArr-arr- = \ f -> refl
        ; _-arr-idArr = \ f -> refl
        ; assoc-arr- = \ f g h -> refl
        }
