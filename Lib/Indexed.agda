module Lib.Indexed where

open import Lib.Basics

_:*:_ : {I : Set}(S T : I -> Set) -> I -> Set
(S :*: T) i = S i * T i
infixr 20 _:*:_

_-:>_ : {I : Set}(S T : I -> Set) -> I -> Set
(S -:> T) i = S i -> T i
infixr 10 _-:>_

[_] : forall {I : Set} -> (I -> Set) -> Set
[ X ] = forall i -> X i
