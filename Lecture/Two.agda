module Lecture.Two where

open import Lib.Basics

open import Lib.Nat

-- VECTORS

open import Lib.Vec

-- 2018-10-04: This definition has moved to the library
-- data Vec (X : Set) : Nat -> Set where
--   []   : Vec X zero
--   _,-_ : forall {n} -> X -> Vec X n -> Vec X (suc n)


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

-- 2018-10-04: This definition has moved to the library
-- _+N_ : Nat -> Nat -> Nat
-- zero +N n = n
-- suc m +N n = suc (m +N n)


_+V_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m +N n) 
[] +V ys = ys
(x ,- xs) +V ys = x ,- (xs +V ys)

-- +V backwards

-- the graph of _+N_ (not needed for this problem)

data Add : Nat -> Nat -> Nat -> Set where
  zero : {n : Nat} -> Add zero n n
  suc : {m n k : Nat} -> Add m n k -> Add (suc m) n (suc k)


data Choppable {X : Set}(m n : Nat) : Vec X (m +N n) -> Set where
  choppable : (xs : Vec X m) -> (ys : Vec X n) -> Choppable m n (xs +V ys) 

chop : {X : Set}(m n : Nat) -> (xs : Vec X (m +N n)) -> Choppable m n xs
chop zero n xs = choppable [] xs
chop (suc m) n (x ,- xs) with chop m n xs
chop (suc m) n (x ,- .(xs +V ys)) | choppable xs ys = choppable (x ,- xs) ys


-- Sg and list2Vec

-- zip backwards?
