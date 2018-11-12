{-# OPTIONS --type-in-type --no-unicode #-}
{- OPTIONS --irrelevant-projections -}
module Lib.Cat.Solver where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.Free

data SynArr {Obj}{Arr : Obj -> Obj -> Set}(C : Category Arr) : Obj -> Obj -> Set
  where
    <_> : forall {S T} -> Arr S T -> SynArr C S T
    idSyn : forall {T} -> SynArr C T T
    _-syn-_ : forall {R S T} -> SynArr C R S -> SynArr C S T ->
               SynArr C R T
    mapSyn : forall
               {Obj'}{Arr' : Obj' -> Obj' -> Set}{C' : Category Arr'}
               {S' T' : Obj'}
               {ObjF : Obj' -> Obj} ->
               (F : Functor C' C ObjF) ->
               SynArr C' S' T' ->
               SynArr C (ObjF S') (ObjF T')
    -[_]- : forall {S T} -> SynArr C S T -> SynArr C S T

infixr 20 _-syn-_

[[_]]Sy : forall {Obj}{S T}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
          SynArr C S T -> Arr S T
[[ < f > ]]Sy = f
[[_]]Sy {C = C} idSyn = idArr where open Category C
[[_]]Sy {C = C} (f -syn- g) = [[ f ]]Sy -arr- [[ g ]]Sy where open Category C
[[ mapSyn F f ]]Sy = map [[ f ]]Sy where open Functor F
[[ -[ f ]- ]]Sy = [[ f ]]Sy

record _=arr=_
  {Obj}{S T : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr}
  (f g : SynArr C S T)
  : Set
  where
    constructor arrEq
    field
      eqArr : [[ f ]]Sy == [[ g ]]Sy
open _=arr=_ public

[=IN_!_=] : forall {Obj}{S T : Obj}{Arr : Obj -> Obj -> Set}(C : Category Arr)
               {d d' : SynArr C S T} ->
               d =arr= d' -> [[ d ]]Sy == [[ d' ]]Sy
[=IN C ! q =] = eqArr q


data MapPile {Obj}{Arr : Obj -> Obj -> Set}(C : Category Arr)
  : Obj -> Obj -> Set
  where
    <_> : forall {S T} -> Arr S T -> MapPile C S T
    mapSyn : forall {Obj'}{Arr' : Obj' -> Obj' -> Set}{C' : Category Arr'}
              {ObjF : Obj' -> Obj}(F : Functor C' C ObjF) ->
              {S' T' : Obj'} -> MapPile C' S' T' ->
              MapPile C (ObjF S') (ObjF T')

module _ where
  [[_]]MP : forall {Obj}{S T : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
            MapPile C S T -> Arr S T
  [[ < f > ]]MP = f
  [[ mapSyn F m ]]MP = map [[ m ]]MP
    where open Functor F

  [[_]]MPs : forall {Obj}{S T : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
            Star (MapPile C) S T -> Arr S T
  [[_]]MPs {C = C} ms = hom C (\ X -> X) [[_]]MP ms

  normSyn : forall {Obj}{S T : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
             SynArr C S T -> Star (MapPile C) S T
  normSyn < f > = < f > ,- []
  normSyn idSyn = []
  normSyn (d -syn- d') = normSyn d +S normSyn d'
  normSyn (mapSyn F d) = star _ (mapSyn F) (normSyn d)
  normSyn -[ d ]- = normSyn d

  .normSynLemma : forall {Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr}{S T} ->
              (d : SynArr C S T) ->
              [[ d ]]Sy == [[ normSyn d ]]MPs
  normSynLemma {C = C} < f > =
    f
      =< f -arr-idArr ]=
    (f -arr- idArr)
      [QED]
    where open Category C
  normSynLemma idSyn = refl
  normSynLemma {C = C} (d -syn- d') =
    ([[ d ]]Sy -arr- [[ d' ]]Sy)
      =[ reff _-arr-_ =$= normSynLemma d =$= normSynLemma d' >=
    ([[ normSyn d  ]]MPs -arr- [[ normSyn d' ]]MPs)
      =< map-arr- (FreeHom C _ [[_]]MP) (normSyn d) (normSyn d') ]=
    [[ normSyn d +S normSyn d' ]]MPs
      [QED]
    where open Category C ; open Functor
  normSynLemma {C = C} (mapSyn F d) =
    map [[ d ]]Sy
      =[ map $= normSynLemma d >=
    map ([[ normSyn d ]]MPs)
      =[ mapHom _ [[_]]MP F (normSyn d) >=
    hom C _ (\ r -> [[ mapSyn F r ]]MP) (normSyn d)
      =< homStar _ (mapSyn F) C _ [[_]]MP (normSyn d) ]=
    [[ star _ (mapSyn F) (normSyn d) ]]MPs
      [QED]
    where open Functor F
  normSynLemma -[ d ]- = normSynLemma d

  .categories :
    forall {Obj}{S T : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
    {d d' : SynArr C S T} ->
    normSyn d == normSyn d' ->
    d =arr= d'
  eqArr (categories {d = d} {d' = d'} q) =
    [[ d ]]Sy
      =[ normSynLemma d >=
    [[ normSyn d ]]MPs
      =[ [[_]]MPs $= q >=
    [[ normSyn d' ]]MPs
      =< normSynLemma d' ]=
    [[ d' ]]Sy
      [QED]

ArrEq : forall {Obj}{S T S' T' : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
           (d : SynArr C S T)(d' : SynArr C S' T') -> Set
ArrEq {S = S}{T}{S'}{T'} d d' =
  Sg (S == S') \ { refl -> Sg (T == T') \ { refl -> d =arr= d' } }

Reduced : forall {Obj}{S T S' T' : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
           (d : SynArr C S T)(d' : SynArr C S' T') -> Set
Reduced (idSyn {T}) (idSyn {T'}) = T == T'
Reduced (f -syn- g) (f' -syn- g') = Reduced f f' * Reduced g g'
Reduced d d' = ArrEq d d'

reduced' : forall {Obj}{S T S' T' : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
  (d : SynArr C S T)(d' : SynArr C S' T') ->
  Reduced d d' ->
  ArrEq d d'
reduced' idSyn idSyn refl = refl , refl , arrEq refl
reduced' (f -syn- g) (f' -syn- g') (rf , rg) with reduced' f f' rf | reduced' g g' rg
reduced' {C = C} (f -syn- g) (f' -syn- g') (rf , rg)
  | refl , refl , arrEq qf | refl , refl , arrEq qg
  = refl , refl , arrEq (reff _-arr-_ =$= qf =$= qg)
  where open Category C
reduced' (d -syn- d1) < x > r = r
reduced' (d -syn- d1) idSyn r = r
reduced' (d -syn- d1) (mapSyn F d') r = r
reduced' (d -syn- d1) -[ d' ]- r = r
reduced' idSyn < x > r = r
reduced' idSyn (d' -syn- d'') r = r
reduced' idSyn (mapSyn F d') r = r
reduced' idSyn -[ d' ]- r = r
reduced' < x > d' r = r
reduced' (mapSyn F d) d' r = r
reduced' -[ d ]- d' r = r

reduced : forall {Obj}{S T}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
  {d d' : SynArr C S T} ->
  Reduced d d' ->
  d =arr= d'
reduced {d = d} {d'} r with reduced' d d' r
... | refl , refl , q = q

rd : forall {Obj}{S T}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
  {d : SynArr C S T} ->
  ArrEq d d
rd = refl , refl , arrEq refl

rq : forall {Obj}{S T}{Arr : Obj -> Obj -> Set}{C : Category Arr} ->
  {d d' : SynArr C S T} ->
  [[ d ]]Sy == [[ d' ]]Sy -> ArrEq d d'
rq q = refl , refl , arrEq q


_=[[_>>=_ : forall {Obj}{S T : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr}
    (d0 : SynArr C S T){d1 d2} ->
    d0 =arr= d1 -> d1 =arr= d2 -> d0 =arr= d2
eqArr (d0 =[[ q1 >>= q2) = [[ d0 ]]Sy =[ eqArr q1 >= eqArr q2

_=<<_]]=_ : forall {Obj}{S T : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr}
    (d0 : SynArr C S T){d1 d2} ->
    d1 =arr= d0 -> d1 =arr= d2 -> d0 =arr= d2
eqArr (d0 =<< q1 ]]= q2) = [[ d0 ]]Sy =< eqArr q1 ]= eqArr q2

_[[QED]] : forall {Obj}{S T : Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr}
    (d : SynArr C S T) -> d =arr= d
eqArr (d [[QED]]) = refl

infixr 10 _=[[_>>=_ _=<<_]]=_
infixr 11 _[[QED]]
