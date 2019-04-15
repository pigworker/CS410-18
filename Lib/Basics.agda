module Lib.Basics where

------------------------------------------------------------------------------

data Zero : Set where

------------------------------------------------------------------------------

record One : Set where
  constructor <>

{-# BUILTIN UNIT One #-}
{-# COMPILE GHC One = data () (()) #-}

------------------------------------------------------------------------------

data Two : Set where
  ff : Two
  tt : Two

{-# BUILTIN BOOL Two #-}
{-# BUILTIN FALSE ff #-}
{-# BUILTIN TRUE tt #-}

------------------------------------------------------------------------------

data List (X : Set) : Set where
  [] : List X
  _,-_ : X -> List X -> List X

infixr 60 _,-_ _+L_

{-# BUILTIN LIST List #-}
{-# COMPILE GHC List = data [] ([] | (:)) #-}

list : forall {X Y} -> (X -> Y) -> List X -> List Y
list f [] = []
list f (x ,- xs) = f x ,- list f xs

_+L_ : forall {X} -> List X -> List X -> List X
[] +L ys = ys
(x ,- xs) +L ys = x ,- xs +L ys

data All {X : Set} (P : X -> Set) : List X -> Set where
  [] : All P []
  _,-_ : forall {x xs} -> P x -> All P xs -> All P (x ,- xs)


------------------------------------------------------------------------------

record Sg {l}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public

_*_ : forall {l} -> Set l -> Set l -> Set l
S * T = Sg S \ _ -> T

infixr 40 _,_
infixr 20 _*_

------------------------------------------------------------------------------

id : forall {l}{X : Set l} -> X -> X
id x = x

_-_ : forall {i j k}
  {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)(g : {a : A}(b : B a) -> C a b) ->
  (a : A) -> C a (f a)
(f - g) a = g (f a)

infixr 50 _-_

------------------------------------------------------------------------------

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

_<+>_ : forall {A B}{P : A + B -> Set}
        (f : (a : A) -> P (inl a))(g : (b : B) -> P (inr b)) ->
        (x : A + B) -> P x
(f <+> g) (inl a) = f a
(f <+> g) (inr b) = g b

either : forall {S T U V : Set} ->
         (S -> U) -> (T -> V) -> (S + T) -> (U + V)
either su tv = (su - inl) <+> (tv - inr)


------------------------------------------------------------------------------

data _==_ {l}{X : Set l}(x : X) : X -> Set where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}

infix 30 _==_

reff : {X : Set}(x : X) -> x == x
reff x = refl

_=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
        f == f' -> x == x' -> f x == f' x'
refl =$= refl = refl

_$=_ : {S : Set}{T : Set}
       (f : S -> T) ->
       {x y : S} -> x == y ->
       f x == f y
f $= q = refl =$= q

_=$_ : {S : Set}{T : S -> Set}{f g : (x : S) -> T x} ->
       (f == g) -> (x : S) -> f x == g x
refl =$ x = refl

_=$: : {X Y : Set}{f f' : .X -> Y}{x x' : X} ->
        f == f' -> f x == f' x'
refl =$: = refl

infixl 20 _=$=_ _$=_ _=$_ _=$:

sym : {X : Set}{x y : X} -> x == y -> y == x
sym refl = refl

_[QED] : {X : Set}(x : X) -> x == x
x [QED] = refl

_=[_>=_ : {X : Set}(x : X){y z : X} -> x == y -> y == z -> x == z
x =[ refl >= q = q

_=<_]=_ : {X : Set}(x : X){y z : X} -> y == x -> y == z -> x == z
x =< refl ]= q = q

infixr 10 _=[_>=_ _=<_]=_
infixr 11 _[QED]
