module Lib.Nat where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- data Nat = Zero | Suc Nat

{-# BUILTIN NATURAL Nat #-}

------------------------------------------------------------------------------

_+N_ : Nat -> Nat -> Nat
zero +N n = n
suc m +N n = suc (m +N n)

infixr 60 _+N_
