module Lecture.Two where

open import Lib.Basics

-- VECTORS

data Vec (X : Set) : Nat -> Set where
  []   : Vec X zero
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

ex : Vec Nat 2
ex = 37 ,- 5 ,- []

-- head

head : {X : Set}{n : Nat} -> Vec X (suc n) -> X
head (x ,- xs) = x
{-
-- head {X} [] = {!!}
head (x ,- xs) = x
-}

-- ex2 = head {Zero} []

-- tail
tail : {X : Set}{n : Nat} -> Vec X (suc n) -> Vec X n
tail (x ,- xs) = xs

-- applicative structure

pure : {n : Nat} -> {X : Set} -> X -> Vec X n
pure {zero} x = []
pure {suc n} x = x ,- pure {n} x

_<*>_ : {n : Nat}{S T : Set} ->
        Vec (S -> T) n -> Vec S n -> Vec T n
[]        <*> []        = []
(f ,- fs) <*> (s ,- ss) = f s ,- (fs <*> ss)

infixl 30 _<*>_

-- map

map : {n : Nat}{S T : Set} ->
      (S -> T) -> Vec S n -> Vec T n
map f ss = pure f <*> ss

-- zip

zip : {n : Nat}{S T : Set} ->
      Vec S n -> Vec T n -> Vec (S * T) n
zip ss ts = pure (_,_) <*> ss <*> ts

ex3 : Nat * Nat
ex3 = 6 , 7

-- +V (necessitating what?)

-- what should the type of vector concatenation be?

_+V_ : {!!}
_+V_ = {!!}

-- +V backwards

-- zip backwards?
