module Lib.Nat where

open import Lib.Basics

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


assoc+N : (m n k : Nat) -> (m +N n) +N k == m +N (n +N k)
assoc+N zero n k =
  (zero +N n) +N k
    =[ refl >=
  n +N k
    =[ refl >=
  n +N k
    =< refl ]=
  zero +N (n +N k)
    [QED]
assoc+N (suc m) n k  =
  (suc m +N n) +N k
    =[ suc $= assoc+N m n k >=
  suc m +N n +N k
    [QED]
  -- suc $= assoc+N m n k

_+Nzero : ∀ n → n +N 0 == n
zero +Nzero = refl
suc n +Nzero = suc $= (n +Nzero)

_+Nsuc_ : (n m : _) → n +N suc m == suc (n +N m)
zero +Nsuc m = refl
suc n +Nsuc m = suc $= (n +Nsuc m)

comm+N : (m n : Nat) -> m +N n == n +N m
comm+N zero n = sym (n +Nzero)
comm+N (suc m) n =
  suc (m +N n)
    =[ suc $= comm+N m n >=
  suc (n +N m)
    =< n +Nsuc m ]=
  n +N suc m
    [QED]

_<=_ : Nat -> Nat -> Set
zero <= y = One
suc x <= zero = Zero
suc x <= suc y = x <= y
