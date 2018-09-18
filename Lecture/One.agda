module Lecture.One where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- data Nat = Zero | Suc Nat

{-# BUILTIN NATURAL Nat #-}

data Two : Set where
  ff : Two
  tt : Two

data Zero : Set where

_<=_ : Nat -> Nat -> Two
zero <= y = tt
suc x <= zero = ff
suc x <= suc y = x <= y

magic : {A : Set} -> Zero -> A
magic ()


