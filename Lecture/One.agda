module Lecture.One where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- data Nat = Zero | Suc Nat

{-# BUILTIN NATURAL Nat #-}

data Two : Set where
  ff : Two
  tt : Two

record One : Set where
  constructor <>

data Zero : Set where

{-
_<=_ : Nat -> Nat -> Two
zero <= y = tt
suc x <= zero = ff
suc x <= suc y = x <= y
-}

_<=_ : Nat -> Nat -> Set
zero <= y = One
suc x <= zero = Zero
suc x <= suc y = x <= y

foo : 5 <= 7
foo = <>

goo : 7 <= 5 -> {X : Set} -> X
goo ()

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

owoto : (x : Nat) -> (y : Nat) -> (x <= y) + (y <= x)
owoto zero y = inl <>
owoto (suc x) zero = inr <>
owoto (suc x) (suc y) = owoto x y

magic : {A : Set} -> Zero -> A
magic ()

data Bound : Set where
  bot : Bound
  val : Nat -> Bound
  top : Bound

_<B=_ : Bound -> Bound -> Set
bot <B= _ = One
_ <B= top = One
val x <B= val y = x <= y
_ <B= _ = Zero

data BST (l u : Bound) : Set where
  node : (x : Nat) -> BST l (val x) -> BST (val x) u -> BST l u
  leaf : l <B= u -> BST l u

insert : {l u : Bound} -> (y : Nat) -> l <B= val y -> val y <B= u -> BST l u -> BST l u
insert y ly yu (node x lx xu) with owoto y x
insert y ly yu (node x lx xu) | inl yx = node x (insert y ly yx lx) xu
insert y ly yu (node x lx xu) | inr xy = node x lx (insert y xy yu xu)
insert y ly yu (leaf p) = node y (leaf ly) (leaf yu)
