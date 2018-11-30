module Lecture.Three where

open import Lib.Basics
open import Lib.Nat

-- Sigma

open import Lib.Vec

ex1 : Sg Nat (λ n → Vec Two n)
ex1 = 2 , (ff ,- (ff ,- []))

ex2 : Nat
ex2 = fst ex1

ex3 : Vec Two (ex1 .fst)
ex3 = snd ex1

_+'_ : Set -> Set -> Set
S +' T = Sg Two λ { ff → S ; tt → T }

-- inl' : {S T : Set} -> S -> S +' T
pattern inl' s = ff , s

-- inr' : {S T : Set} -> T -> S +' T
pattern inr' t = tt , t

swap : {S T : Set} -> S +' T -> T +' S
swap (inl' s) = inr' s
swap (inr' t) = inl' t

-- list2vec

list2Vec : {X : Set} -> List X -> Sg Nat \ n -> Vec X n
list2Vec [] = _ , []
list2Vec (x ,- xs) with list2Vec xs
list2Vec (x ,- xs) | _ , xs' = _ , (x ,- xs')

-- equality

-- equational reasoning combinators

assoc : (m n k : Nat) -> (m +N n) +N k == m +N (n +N k)
assoc zero n k =
  (zero +N n) +N k
    =[ refl >=
  n +N k
    =[ refl >=
  n +N k
    =< refl ]=
  zero +N (n +N k)
    [QED]
assoc (suc m) n k  =
  (suc m +N n) +N k
    =[ suc $= assoc m n k >=
  suc m +N n +N k
    [QED]
  -- suc $= assoc m n k

{- moved to Lib.nat
_+Nzero : ∀ n → n +N 0 == n
zero +Nzero = refl
suc n +Nzero = suc $= (n +Nzero)

_+Nsuc_ : (n m : _) → n +N suc m == suc (n +N m)
zero +Nsuc m = refl
suc n +Nsuc m = suc $= (n +Nsuc m)
-}

comm : (m n : Nat) -> m +N n == n +N m
comm zero n = sym (n +Nzero)
comm (suc m) n =
  suc (m +N n)
    =[ suc $= comm m n >=
  suc (n +N m)
    =< n +Nsuc m ]=
  n +N suc m
    [QED]
