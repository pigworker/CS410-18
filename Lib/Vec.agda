module Lib.Vec where

open import Lib.Basics
open import Lib.Nat

data Vec (X : Set) : Nat -> Set where
  []   : Vec X zero
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

vPure : {n : Nat}{X : Set} -> X -> Vec X n
vPure {zero} x = []
vPure {suc n} x = x ,- vPure x

_<*V>_ : forall {n}{X Y : Set} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
[] <*V> [] = []
(f ,- fs) <*V> (x ,- xs) = f x ,- fs <*V> xs
infixl 80 _<*V>_

vec : forall {n}{X Y : Set} -> (X -> Y) -> Vec X n -> Vec Y n
vec = vPure - _<*V>_

_+V_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m +N n) 
[] +V ys = ys
(x ,- xs) +V ys = x ,- (xs +V ys)

data Choppable {X : Set}(m n : Nat) : Vec X (m +N n) -> Set where
  choppable : (xs : Vec X m) -> (ys : Vec X n) -> Choppable m n (xs +V ys) 

chop : {X : Set}(m n : Nat) -> (xs : Vec X (m +N n)) -> Choppable m n xs
chop zero n xs = choppable [] xs
chop (suc m) n (x ,- xs) with chop m n xs
chop (suc m) n (x ,- .(xs +V ys)) | choppable xs ys = choppable (x ,- xs) ys

Matrix : Set -> Nat * Nat -> Set
Matrix C (w , h) = Vec (Vec C w) h

vecFoldR : {X Y : Set} -> (X -> Y -> Y) -> Y -> {n : Nat} -> Vec X n -> Y
vecFoldR c n [] = n
vecFoldR c n (x ,- xs) = c x (vecFoldR c n xs)
