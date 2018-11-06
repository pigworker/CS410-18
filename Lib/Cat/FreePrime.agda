{-# OPTIONS --type-in-type --no-unicode #-}
-- {-# OPTIONS --irrelevant-projections #-}
module Lib.Cat.FreePrime where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor

-- reflexive-transitive closure of a relation R

data Star {X : Set}(R : X -> X -> Set)(x : X) : X -> Set where
  [] : Star R x x
  _,-_ : {y z : X} -> R x y -> Star R y z -> Star R x z

List' : Set -> Set
List' A = Star {One} (\ _ _ -> A) <> <>


_+S_ : forall {X : Set}{R : X -> X -> Set}{x y z : X} ->
        Star R x y -> Star R y z -> Star R x z
[] +S gs = gs
(f ,- fs) +S gs = f ,- (fs +S gs)


_+S[] : forall {X : Set}{R : X -> X -> Set}{x y : X} ->
        (fs : Star R x y) -> (fs +S []) == fs
[] +S[] = refl
(f ,- fs) +S[] = (f ,-_) $= (fs +S[])

assoc+S : forall {X : Set}{R : X -> X -> Set}{w x y z : X} ->
  (fs : Star R w x)(gs : Star R x y)(hs : Star R y z) ->
  ((fs +S gs) +S hs) == (fs +S (gs +S hs))
assoc+S [] gs hs = refl
assoc+S (f ,- fs) gs hs = (f ,-_) $= assoc+S fs gs hs


-- free category on a relation R

FREE : {X : Set}(R : X -> X -> Set) -> Category (Star R)
FREE R = record
           { idArr = []
           ; _-arr-_ = _+S_
           ; idArr-arr- = \ f -> refl
           ; _-arr-idArr = _+S[]
           ; assoc-arr- = assoc+S
           }

-- to give a functor FREE R -> C, it is enough to give a function
-- F : X -> Obj_C such that related elements are connected by an arrow

module _ {X : Set}{R : X -> X -> Set}
         {Obj}{Arr : Obj -> Obj -> Set}(C : Category Arr)
         (ObjF : X -> Obj)
         (f : {x x' : X} -> R x x' -> Arr (ObjF x) (ObjF x')) where
  open Category C
  open Functor

  hom : {x x' : X} -> Star R x x' -> Arr (ObjF x) (ObjF x')
  hom [] = idArr
  hom (r ,- rs) = f r -arr- hom rs

  FreeHom : Functor (FREE R) C ObjF
  map FreeHom = hom
  mapidArr FreeHom = refl
  map-arr- FreeHom [] rs' =  hom rs' =< idArr-arr- (hom rs') ]= (idArr -arr- hom rs') [QED]
  map-arr- FreeHom (r ,- rs) rs' =
      (f r -arr- hom (rs +S rs'))
        =[ (f r -arr-_) $= map-arr- FreeHom rs rs' >=
      (f r -arr- (hom rs -arr- hom rs'))
        =< assoc-arr- _ _ _ ]=
      ((f r -arr- hom rs) -arr- hom rs')
        [QED]

homSpecial : {X : Set}{R : X -> X -> Set} {x x' : X} -> Star (Star R) x x' -> Star R x x'
homSpecial {R = R} = hom (FREE R) id id



module _ {X : Set}{R : X -> X -> Set}
         {Obj}{Arr : Obj -> Obj -> Set}(C : Category Arr)
         (ObjF : X -> Obj)(F : Functor (FREE R) C ObjF) where

  open Functor F
  
  Underlying : {x x' : X} -> R x x' -> Arr (ObjF x) (ObjF x')
  Underlying r = map (r ,- [])


-- the FREE construction is functorial: if there is an arrow between
-- the relations R : X -> X -> Set and S : Y -> Y -> Set, then there
-- is a functor FREE R -> FREE S

star : forall {X : Set}{R : X -> X -> Set}{Y : Set}{S : Y -> Y -> Set}
              (F : X -> Y)(f : {x x' : X} -> R x x' -> S (F x) (F x')) ->
              {x x' : X} -> Star R x x' -> Star S (F x) (F x')
star {S = S} F f = hom (FREE S) F \ r -> f r ,- []

homStar : forall
          {X : Set}{R : X -> X -> Set}{Y : Set}{S : Y -> Y -> Set}
          (F : X -> Y)(f : {x x' : X} -> R x x' -> S (F x) (F x'))
          {Obj}{Arr : Obj -> Obj -> Set}(C : Category Arr)
          (G : Y -> Obj)(g : {y y' : Y} -> S y y' -> Arr (G y) (G y'))
          {x x' : X}(rs : Star R x x') ->
          hom C G g (star F f rs) == hom C (F - G) (f - g) rs
homStar F f C G g [] = refl
homStar F f C G g (r ,- rs) = (g (f r) -arr-_) $= homStar F f C G g rs
  where open Category C


{-
-- liftings (R -> C) -> (Free R -> C) commutes with composition

module _ {X : Set}{R : X -> X -> Set}
         {Obj}{Arr : Obj -> Obj -> Set}{C : Category Arr}
         (F : X -> Obj)(f : {x x' : X} -> R x x' -> Arr (F x) (F x'))
         {Obj'}{Arr' : Obj' -> Obj' -> Set}{C' : Category Arr'}
         {ObjG : Obj -> Obj'}(G : Functor C C' ObjG)
         where

  open Functor G
  private module S = Category C
  private module T = Category C'

  .mapHom : forall {x x'}(rs : Star R x x') ->
            map (hom C F f rs) == hom C' (F - ObjG) (f - map) rs
  mapHom [] = mapidArr
  mapHom (r ,- rs) =
     map (f r S.-arr- hom C F f rs)
       =[ map-arr- _ _ >=
     (map (f r) T.-arr- map (hom C F f rs))
       =[ (map (f r) T.-arr-_) $= mapHom rs  >=
     (map (f r) T.-arr- hom C' _ (f - map) rs)
       [QED]
-}
