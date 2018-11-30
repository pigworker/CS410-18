module Lib.Vec where

open import Lib.Nat

data Vec (X : Set) : Nat -> Set where
  []   : Vec X zero
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

vPure : {n : Nat}{X : Set} -> X -> Vec X n
vPure {zero} x = []
vPure {suc n} x = x ,- vPure x
