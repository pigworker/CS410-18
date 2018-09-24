module Lecture.Two where

open import Lib.Basics

-- VECTORS

data Vec (X : Set) : Nat -> Set where
  []   : Vec X zero
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

-- head

-- tail

-- applicative structure

-- map

-- zip

-- +V (necessitating what?)

-- +V backwards

-- zip backwards?
