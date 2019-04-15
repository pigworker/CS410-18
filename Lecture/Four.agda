{-# OPTIONS --type-in-type --no-unicode #-}
{- OPTIONS --irrelevant-projections -}
module Lecture.Four where

open import Lib.Basics
open import Lib.Nat
open import Lib.Vec
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.NatTrans
open import Lib.Cat.ProductCat
open import Lib.Cat.Solver
open import Lib.Cat.Monad


-- recap (NaturalTransformation, singletonNT)                -- C
-- what has changed? (making equations irrelevant, ID C)     -- C
-- what next?
--   Functor composition                                     -- F
--   Category of Categories                                  -- F
--   Definition of Monad                                     -- C
--   what is join for LIST?                                  -- F
--   concat as a natural transformation                      -- F
--     define concat; it needs append                        -- F
--     naturality of concat needs naturality of append       -- F
--   how can we state the naturality of append?
--     need to work with pairs of things
-- *Cat and *Fun                                             -- C
-- Delta and SETPair                                         -- C
-- construct append as a natural transformation              -- F
-- complete concat as a natural transformation               -- F
-- see what we have to prove to build the LIST monad         -- F
-- cliffhanger, roll credits

{- moved to Lib.Cat.Category
postulate
  ext : {S : Set}{T : S -> Set}{f g : (x : S) -> T x} ->
        ((x : S) -> f x == g x) -> f == g

record Category {Obj : Set}(Arr : Obj -> Obj -> Set) : Set where
  field
    -- structure
    idArr       : {X : Obj} -> Arr X X
    _-arr-_     : {R S T : Obj} -> Arr R S -> Arr S T -> Arr R T
    -- laws
    .idArr-arr-  : {S T : Obj}(f : Arr S T) -> (idArr -arr- f) == f
    ._-arr-idArr : {S T : Obj}(f : Arr S T) -> (f -arr- idArr) == f
    .assoc-arr-  : {R S T U : Obj}
                   (f : Arr R S)(g : Arr S T)(h : Arr T U) ->
                   ((f -arr- g) -arr- h) == (f -arr- (g -arr- h))
  infixr 20 _-arr-_

SomeCategory : Set
SomeCategory = Sg Set                 \ Obj ->
               Sg (Obj -> Obj -> Set) \ Arr ->
               Category Arr

SET : Category \ S T -> S -> T
SET = record
        { idArr = λ z → z
        ; _-arr-_ = λ f g → λ r → g (f r)
        ; idArr-arr- = λ f → refl
        ; _-arr-idArr = λ f → refl
        ; assoc-arr- = λ f g h → refl
        }
-}

refl-LE : (n : Nat) -> n <= n
refl-LE zero = <>
refl-LE (suc n) = refl-LE n

trans-LE : (x y z : Nat) -> x <= y -> y <= z -> x <= z
trans-LE zero y z xy yz = <>
trans-LE (suc x) zero z () yz
trans-LE (suc x) (suc y) zero xy ()
trans-LE (suc x) (suc y) (suc z) xy yz = trans-LE x y z xy yz

irrelevant-LE : (x y : Nat) (p q : x <= y) -> p == q
irrelevant-LE zero y p q = refl
irrelevant-LE (suc x) zero p ()
irrelevant-LE (suc x) (suc y) p q = irrelevant-LE x y p q

NAT-LE : Category _<=_
NAT-LE = record
           { idArr = \ {X} -> refl-LE X
           ; _-arr-_ = \ {x}{y}{z} -> trans-LE x y z
           ; idArr-arr- = \ {x}{y} f -> irrelevant-LE x y _ _
           ; _-arr-idArr = \ {x}{y} f -> irrelevant-LE x y _ _
           ; assoc-arr- = \ {x}{y}{z}{w} f g h -> irrelevant-LE x w _ _
           }

{- moved to Lib.Cat.Category
_^op : forall {Obj}{Arr : Obj -> Obj -> Set} ->
       Category Arr -> Category \ S T -> Arr T S
C ^op = record
          { idArr = idArr
          ; _-arr-_ = \ g f -> f -arr- g
          ; idArr-arr- = \ f -> f -arr-idArr
          ; _-arr-idArr = \ f -> idArr-arr- f
          ; assoc-arr- = \ f g h -> sym (assoc-arr- h g f)
          }
  where open Category C
-}

ADDITION : Category {One} \ _ _ -> Nat
ADDITION = record
             { idArr = 0
             ; _-arr-_ = _+N_
             ; idArr-arr- = \n -> refl
             ; _-arr-idArr = _+Nzero
             ; assoc-arr- = assoc+N
             }

record Preorder {X : Set}(_<?=_ : X -> X -> Set) : Set where
  field
    reflexive   : {x : X} -> x <?= x
    transitive  : {x y z : X} ->
                  x <?= y -> y <?= z -> x <?= z
    irrelevant  : {x y : X}{p q : x <?= y} -> p == q

SomePreorder : Set1
SomePreorder =
  Sg Set             \ X ->
  Sg (X -> X -> Set) \ _<?=_ ->
  Preorder _<?=_

record MonotoneMap (XP YP : SomePreorder) : Set where
  field
    mapData     : fst XP -> fst YP
    .mapMonotone :
      let X , _<X=_ , _ = XP
          Y , _<Y=_ , _ = YP
      in  {x0 x1 : X} -> x0 <X= x1 ->
                 mapData x0 <Y= mapData x1

PREORDER : Category MonotoneMap
PREORDER = record
             { idArr = record { mapData = id ; mapMonotone = id }
             ; _-arr-_ = \ f g ->
               record { mapData = mapData f - mapData g
                      ; mapMonotone = \ p -> (mapMonotone g) (mapMonotone f p)
                      }
             ; idArr-arr- = \ f -> refl
             ; _-arr-idArr = \ f  -> refl
             ; assoc-arr- = \ f g h -> refl
             }
  where open MonotoneMap

{- moved to Lib.Cat.Functor
record Functor
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}(CatS : Category ArrS)
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}(CatT : Category ArrT)
  (ObjF : ObjS -> ObjT)
  : Set where
  module S = Category CatS
  module T = Category CatT
  field
    map      : forall {A B : ObjS} -> ArrS A B -> ArrT (ObjF A) (ObjF B)
    -- laws
    .mapidArr : forall {A} -> map (S.idArr {A}) == T.idArr {ObjF A}
    .map-arr- : forall {A B C}(f : ArrS A B)(g : ArrS B C) ->
                map (f S.-arr- g) == (map f T.-arr- map g)

SomeFunctor : SomeCategory -> SomeCategory -> Set
SomeFunctor (ObjS , ArrS , CatS) (ObjT , ArrT , CatT) =
   Sg (ObjS -> ObjT) \ ObjF ->
   Functor CatS CatT ObjF
-}

list : {A B : Set} -> (A -> B) -> List A -> List B
list f [] = []
list f (a ,- as) = f a ,- list f as

listId : forall {A} (as : List A) -> list (\ z -> z) as == as
listId [] = refl
listId (a ,- as) = (a ,-_) $= listId as   --  (a ,-_) is Haskell's (a :)

listComp : forall {A B C} {f : A -> B} {g : B -> C} (as : List A) ->
           list (\ r -> g (f r)) as == list g (list f as)
listComp [] = refl
listComp (a ,- as) = (_ ,-_) $= listComp as

LIST : Functor SET SET List
LIST = record { map = list ; mapidArr = ext listId ; map-arr- = \ f g -> ext listComp }

{- moved to Lib.Cat.Functor
ID : {Obj : Set}{Arr : Obj -> Obj -> Set}(C : Category Arr) -> Functor C C \ X -> X
ID C = record { map = \ f -> f ; mapidArr = refl ; map-arr- = \ f g -> refl }
-}

{-
ID : Functor SET SET \ X -> X
ID = record { map = \ f -> f
            ; mapidArr = refl
            ; map-arr- = \ f g -> refl
            }
-}

{- moved to Lib.Cat.Functor
module _
  {ObjR : Set}{ArrR : ObjR -> ObjR -> Set}{CatR : Category ArrR}
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
  {ObjF : ObjR -> ObjS}
  {ObjG : ObjS -> ObjT}
  where
  private
    module R = Category CatR
    module S = Category CatS
    module T = Category CatT

  _-Func-_ :  Functor CatR CatS ObjF
           ->
              Functor CatS CatT ObjG
           ->
              Functor CatR CatT \ X -> ObjG (ObjF X)
  Functor.map (F -Func- G) f = G.map (F.map f)
    where
    module F = Functor F
    module G = Functor G
  Functor.mapidArr (F -Func- G) =
      G.map (F.map R.idArr)
        =[ G.map $= F.mapidArr >=
      G.map S.idArr
        =[ G.mapidArr >=
      T.idArr
        [QED]
    where
    module F = Functor F
    module G = Functor G
  Functor.map-arr- (F -Func- G) f g =
      G.map (F.map (f R.-arr- g))
        =[ G.map $= F.map-arr- f g >=
      G.map (F.map f S.-arr- F.map g)
        =[ G.map-arr- (F.map f) (F.map g) >=
      (G.map (F.map f) T.-arr- G.map (F.map g))
        [QED]
    where
    module F = Functor F
    module G = Functor G

  infixr 20 _-Func-_

CATEGORY : Category SomeFunctor
CATEGORY = record
             { idArr = _ , ID _
             ; _-arr-_ = \ { (ObjF , F) (ObjG , G) -> _ , (F -Func- G) }
             ; idArr-arr- = \ F -> refl
             ; _-arr-idArr = \ F -> refl
             ; assoc-arr- = \ F G H -> refl
             }
-}

{-
VEC : (n : Nat) -> Functor SET SET (\ X -> Vec X n)
VEC n = record { map = {!!} ; mapidArr = {!!} ; map-arr- = {!!} }
-}

take : {X : Set}{A B : Nat} -> B <= A -> Vec X A -> Vec X B
take {X} {m} {zero} p xs = []
take {X} {.0} {suc n} () []
take {X} {(suc m)} {suc n} p (x ,- xs) = x ,- take p xs

takeAll : forall {X n} (xs : Vec X n) -> take (refl-LE n) xs == xs
takeAll [] = refl
takeAll (x ,- xs) = (x ,-_) $= takeAll xs

takeComp : forall a b c (ba : b <= a) (cb : c <= b) {X} (xs : Vec X a) ->
           take {B = c} (trans-LE c b a cb ba) xs ==
            take  cb (take ba xs)
takeComp a b zero ba cb xs = refl
takeComp .0 zero (suc c) ba () []
takeComp .0 (suc b) (suc c) () cb []
takeComp .(suc _) zero (suc c) ba () (x ,- xs)
takeComp (suc a) (suc b) (suc c) ba cb (x ,- xs) =
-- takeComp .(suc a) (suc b) (suc c) ba cb (_,-_ {n = a} x xs) =
  (x ,-_) $= takeComp a b c ba cb xs

TAKE : (X : Set) -> Functor (NAT-LE ^op) SET (Vec X)
TAKE X = record
  { map = take
  ; mapidArr = ext takeAll
  ; map-arr- = \ {a}{b}{c} ba cb -> ext (takeComp a b c ba cb)
  }

{- moved to Lib.Cat.NatTrans
record NaturalTransformation
  {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
  {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
  {ObjF : ObjS -> ObjT}(F : Functor CatS CatT ObjF)
  {ObjG : ObjS -> ObjT}(G : Functor CatS CatT ObjG)
  : Set where
  open Category CatT
  open Functor
  field
    transform : (X : ObjS) -> ArrT (ObjF X) (ObjG X)
    .natural : {X Y : ObjS} -> (f : ArrS X Y) ->
               (transform X -arr- map G f) == (map F f -arr- transform Y)
-}

module _ where
  open NaturalTransformation
  singletonNT : NaturalTransformation (ID SET) LIST
  transform singletonNT X x = x ,- []
  natural singletonNT f = refl

{- moved to Lib.Cat.Monad
record Monad {Obj : Set}{Arr : Obj -> Obj -> Set}{C : Category Arr}
             {ObjM : Obj -> Obj}
             (M : Functor C C ObjM) : Set where
  open Category C
  open Functor M
  field
    returnNT : NaturalTransformation (ID C) M
    joinNT   : NaturalTransformation (M -Func- M) M
  module R = NaturalTransformation returnNT
  module J = NaturalTransformation joinNT
  field
    returnJoin : {X : Obj} ->
      (R.transform (ObjM X) -arr- J.transform X) == idArr
    mapReturnJoin : {X : Obj} ->
      (map (R.transform X) -arr- J.transform X) == idArr
    joinJoin : {X : Obj} ->
      (J.transform (ObjM X) -arr- J.transform X)
      ==
      (map (J.transform X) -arr- J.transform X)
  KlArr : Obj -> Obj -> Set
  KlArr S T = Arr S (ObjM T)
  Kleisli : Category KlArr
  Kleisli = record
    { idArr = R.transform _
    ; _-arr-_ = \ h k -> h -arr- map k -arr- J.transform _
    ; idArr-arr- = \ {S} {T} f ->
      [=IN C !
      (< R.transform S > -syn- (mapSyn M < f > -syn- < J.transform T >))
        =[[ categories refl >>=
      (-[ < R.transform S > -syn- mapSyn M < f > ]- -syn- < J.transform T >)
        =[[ reduced (rq (R.natural f) , rd) >>=
      (-[ < f > -syn- < R.transform (ObjM T) > ]- -syn- < J.transform T >)
        =[[ categories refl >>=
      (< f > -syn- -[ < R.transform (ObjM T) > -syn- < J.transform T > ]-)
        =[[ reduced (rd , rq returnJoin) >>=
      (< f > -syn- -[ idSyn ]-)
        =[[ categories refl >>=
      < f >
        [[QED]]
      =]
      {-
      (R.transform S -arr- (map f -arr- J.transform T))
        =< assoc-arr- _ _ _ ]=
      ((R.transform S -arr- map f) -arr- J.transform T)
        =[ (_-arr- J.transform T) $= R.natural f  >=
      ((f -arr- R.transform (ObjM T)) -arr- J.transform T)
         =[ assoc-arr- _ _ _ >=
      (f -arr- R.transform (ObjM T) -arr- J.transform T)
        =[ (f -arr-_) $= returnJoin >=
      (f -arr- idArr)
        =[ f -arr-idArr >=
      f
        [QED]
      -}
    ; _-arr-idArr = \ {S} {T} f ->
      (f -arr- (map (R.transform T) -arr- J.transform T))
        =[ (f -arr-_) $= mapReturnJoin >=
      (f -arr- idArr)
        =[ Category._-arr-idArr C f >=
      f
        [QED]
    ; assoc-arr- = \ {R}{S}{T}{U} f g h ->
      [=IN C !
      ((< f > -syn- mapSyn M < g > -syn- < J.transform T >) -syn- mapSyn M < h > -syn- < J.transform U >)
          =[[ categories refl >>=
      (< f > -syn- mapSyn M < g > -syn- -[ < J.transform T > -syn- mapSyn M < h > ]- -syn- < J.transform U >)
          =[[ reduced (rd , rd , rq (J.natural h) , rd) >>=
      (< f > -syn- mapSyn M < g > -syn- -[ mapSyn M (mapSyn M < h >) -syn- < J.transform (ObjM U) > ]-
                                                                                    -syn- < J.transform U >)
          =[[ categories refl >>=
      (< f > -syn- mapSyn M < g > -syn- mapSyn M (mapSyn M < h >) -syn-
               -[ < J.transform (ObjM U) > -syn- < J.transform U > ]-)
          =[[ reduced (rd , rd , rd , rq joinJoin) >>=
      (< f > -syn- mapSyn M < g > -syn- mapSyn M (mapSyn M < h >) -syn-
               -[ mapSyn M < J.transform U > -syn- < J.transform U > ]-)
          =[[ categories refl >>=
      (< f > -syn- mapSyn M (< g > -syn- mapSyn M < h > -syn- < J.transform U >) -syn- < J.transform U >)
         [[QED]]
      =]
      {-
      (f -arr- map g -arr- J.transform T) -arr- map h -arr- J.transform U
         =[ {!!} >=  --boring assoc
      f -arr- map g -arr- (J.transform T -arr- map h) -arr- J.transform U
         =[ (\ z -> f -arr- map g -arr- z -arr- J.transform U) $= J.natural h >=
      f -arr- map g -arr- (map (map h) -arr- J.transform (ObjM U)) -arr- J.transform U
         =[ {!!} >= -- boring assoc
      f -arr- map g -arr- map (map h) -arr- J.transform (ObjM U) -arr- J.transform U
         =[ {!!} >= -- boring assoc
      f -arr- map g -arr- map (map h) -arr- (J.transform (ObjM U) -arr- J.transform U)
         =[ (\ z -> f -arr- map g -arr- map (map h) -arr- z) $= joinJoin >=
      f -arr- map g -arr- map (map h) -arr- (map (J.transform U) -arr- J.transform U)
         =[ {!!} >= -- boring functoriality + assoc
      f -arr- map (g -arr- map h -arr- J.transform U) -arr- J.transform U
         [QED]
      -}
    }
-}

{- moved to Lib.Cat.ProductCat
_*Cat_ : {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}(CatS : Category ArrS)
         {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}(CatT : Category ArrT) ->
         Category {ObjS * ObjT} \ {(SS , TS) (ST , TT) ->
           ArrS SS ST * ArrT TS TT}
CatS *Cat CatT =
  record
    { idArr = (S.idArr , T.idArr)
    ; _-arr-_ = \ { (fS , fT) (gS , gT) -> (fS S.-arr- gS) , (fT T.-arr- gT) }
    ; idArr-arr- = \ { {AS , AT} {BS , BT} (fS , fT) ->
                          reff _,_ =$= (Category.idArr-arr- CatS fS) =$= (Category.idArr-arr- CatT fT) }
    ; _-arr-idArr = \ { {AS , AT} {BS , BT} (fS , fT) ->
                          reff _,_ =$= (Category._-arr-idArr CatS fS) =$= (Category._-arr-idArr CatT fT) }
    ; assoc-arr- = \ { (fS , fT) (gS , gT) (hS , hT) -> reff _,_ =$= Category.assoc-arr- CatS fS gS hS =$= Category.assoc-arr- CatT fT gT hT }
    }
  where
    module S = Category CatS
    module T = Category CatT

module _
         {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS}
         {ObjT : Set}{ArrT : ObjT -> ObjT -> Set}{CatT : Category ArrT}
         {ObjF : ObjS -> ObjT}(F : Functor CatS CatT ObjF)
         {ObjS' : Set}{ArrS' : ObjS' -> ObjS' -> Set}{CatS' : Category ArrS'}
         {ObjT' : Set}{ArrT' : ObjT' -> ObjT' -> Set}{CatT' : Category ArrT'}
         {ObjF' : ObjS' -> ObjT'}(F' : Functor CatS' CatT' ObjF')
  where
    private
      module F = Functor F
      module F' = Functor F'
      open Functor

    _*Fun_ :
         Functor (CatS *Cat CatS') (CatT *Cat CatT')
           \ { (S , S') -> (ObjF S , ObjF' S') }
    map _*Fun_ (f , f') = (F.map f) , (F'.map f')
    mapidArr _*Fun_ = reff _,_ =$= F.mapidArr =$= F'.mapidArr
    map-arr- _*Fun_ (f , f') (g , g') =
      reff _,_ =$= F.map-arr- f g =$= F'.map-arr- f' g'
-}

module _ {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS} where
  open Category CatS
  open Functor


  Delta : Functor CatS (CatS *Cat CatS) \ X -> X , X
  Delta = record
    { map = \ f -> f , f
    ; mapidArr = refl
    ; map-arr- = \ f g -> refl
    }

module _ where
  open Category SET
  open Functor

  SETPair : Functor (SET *Cat SET) SET \ { (S , T) -> S * T }
  map SETPair (f , f') (a , a') = (f a) , (f' a')
  mapidArr SETPair = refl
  map-arr- SETPair (f , f') (g , g') = refl

module _ where
  open NaturalTransformation

  _+L_ : {X : Set} -> List X -> List X -> List X
  [] +L ys = ys
  (x ,- xs) +L ys = x ,- (xs +L ys)

  appendNatural : {X Y : Set}(f : X -> Y)(xs ys : List X) ->
                   list f (xs +L ys) == (list f xs +L list f ys)
  appendNatural f [] ys = refl
  appendNatural f (x ,- xs) ys = (f x ,-_) $= appendNatural f xs ys

  appendNT : NaturalTransformation (Delta -Func- (LIST *Fun LIST) -Func- SETPair)
                                   LIST
  appendNT = record { transform = \ X -> \ { (xs , ys) -> xs +L ys }
                    ; natural = \ f -> ext \ { (xs , ys) -> appendNatural f xs ys }
                    }

  concat : {X : Set} -> List (List X) -> List X
  concat [] = []
  concat (xs ,- xss) = xs +L concat xss

  concatNatural : forall {X Y} (f : X -> Y) (xss : List (List X)) ->
                  list f (concat xss) == concat (list (list f) xss)
  concatNatural f [] = refl
  concatNatural f (xs ,- xss) =
    list f (xs +L concat xss)
      =[ appendNatural f xs (concat xss) >=
    (list f xs +L list f (concat xss))
      =[ (list f xs +L_) $= concatNatural f xss >=
    (list f xs +L concat (list (list f) xss))
      [QED]

  concatNT : NaturalTransformation (LIST -Func- LIST) LIST
  transform concatNT X = concat
  natural concatNT f = ext (concatNatural f)

_+L[] : {X : Set} -> (xs : List X) -> (xs +L []) == xs
[] +L[] = refl
(x ,- xs) +L[] = (x ,-_) $= (xs +L[])

concatMapSing : {X : Set} -> (xs : List X) ->
                 concat (list (\ x -> x ,- []) xs) == xs
concatMapSing [] = refl
concatMapSing (x ,- xs) = (x ,-_) $= concatMapSing xs

assoc+L : {X : Set} (xs ys zs : List X) -> ((xs +L ys) +L zs) == (xs +L (ys +L zs))
assoc+L [] ys zs = refl
assoc+L (x ,- xs) ys zs = (x ,-_) $= assoc+L xs ys zs

concatAppend : {X : Set} -> (xss yss : List (List X)) ->
               concat (xss +L yss) == (concat xss +L concat yss)
concatAppend [] yss = refl
concatAppend (xs ,- xss) yss =
  (xs +L concat (xss +L yss))
    =[ (xs +L_) $= concatAppend xss yss >=
  (xs +L (concat xss +L concat yss))
      =< assoc+L xs _ _ ]=
  ((xs +L concat xss) +L concat yss)
    [QED]

concatConcat : {X : Set} -> (xs : List (List (List X))) ->
                concat (concat xs) == concat (list concat xs)
concatConcat [] = refl
concatConcat (xss ,- xsss) =
  concat (xss +L concat xsss)
    =[ concatAppend xss _ >=
  (concat xss +L concat (concat xsss))
    =[ (concat xss +L_) $= concatConcat xsss >=
  (concat xss +L concat (list concat xsss))
    [QED]

LISTMonad : Monad LIST
LISTMonad = record
              { returnNT = singletonNT
              ; joinNT = concatNT
              ; returnJoin = ext _+L[]
              ; mapReturnJoin = ext concatMapSing
              ; joinJoin = ext concatConcat
              }







{- here are some we made earlier

  Kleisli : Category KlArr
  Kleisli = record
    { idArr = R.transform _
    ; _-arr-_ = \ h k -> h -arr- map k -arr- J.transform _
    ; idArr-arr- = {!!}
    ; _-arr-idArr = {!!}
    ; assoc-arr- = {!!}
    }


  F -Func- G = record
    { map      = \ ab -> G.map (F.map ab)
    ; mapidArr =
        G.map (F.map R.idArr)
          =[ G.map $= F.mapidArr >=
        G.map S.idArr
          =[ G.mapidArr >=
        T.idArr
          [QED]
    ; map-arr- = \ h k ->
        G.map (F.map (h R.-arr- k))
          =[ G.map $= F.map-arr- h k >=
        G.map (F.map h S.-arr- F.map k)
          =[ G.map-arr- (F.map h) (F.map k) >=
        (G.map (F.map h) T.-arr- G.map (F.map k))
          [QED]
    }


CATEGORY = record
  { idArr = \ { {_ , _ , C} -> _ , ID C }
  ; _-arr-_ = \ { (ObjF , F) (ObjG , G) -> _ , (F -Func- G) }
  ; idArr-arr-  = \ _ -> refl
  ; _-arr-idArr = \ _ -> refl
  ; assoc-arr-  = \ _ _ _ -> refl
  }

CatS *Cat CatT = record
  { idArr = S.idArr , T.idArr
  ; _-arr-_ = \ { (fS , fT) (gS , gT) -> (fS S.-arr- gS) , (fT T.-arr- gT) }
  ; idArr-arr- = \ { (fS , fT) -> reff _,_ =$= S.idArr-arr- fS =$= T.idArr-arr- fT }
  ; _-arr-idArr = \ { (fS , fT) -> reff _,_ =$= (fS S.-arr-idArr) =$= (fT T.-arr-idArr) }
  ; assoc-arr- = \ { (fS , fT) (gS , gT) (hS , hT) ->
     reff _,_ =$= S.assoc-arr- fS gS hS =$= T.assoc-arr- fT gT hT }
  }
  where
    module S = Category CatS
    module T = Category CatT

    _*Fun_ :
         Functor (CatS *Cat CatS') (CatT *Cat CatT') \ { (S , S') -> (ObjF S , ObjF' S') }
    map _*Fun_ (f , f') = F.map f , F'.map f'
    mapidArr _*Fun_ = reff _,_ =$= F.mapidArr =$= F'.mapidArr
    map-arr- _*Fun_ (f , f') (g , g') = reff _,_ =$= F.map-arr- f g =$= F'.map-arr- f' g'



module _ {ObjS : Set}{ArrS : ObjS -> ObjS -> Set}{CatS : Category ArrS} where
  open Category CatS
  open Functor

  Delta : Functor CatS (CatS *Cat CatS) \ X -> X , X
  map Delta f = f , f
  mapidArr Delta = refl
  map-arr- Delta _ _ = refl

module _ where
  open Category SET
  open Functor

  SETPair : Functor (SET *Cat SET) SET \ { (S , T) -> S * T }
  map SETPair (f , g) (a , b) = f a , g b
  mapidArr SETPair = refl
  map-arr- SETPair f g = refl



_+L_ : {X : Set} -> List X -> List X -> List X
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)

concat : {X : Set} -> List (List X) -> List X
concat [] = []
concat (xs ,- xss) = xs +L concat xss

appendNatural : forall {X Y} (f : X -> Y) (xs ys : List X) ->
                list f (xs +L ys) == (list f xs +L list f ys)
appendNatural f [] ys = refl
appendNatural f (x ,- xs) ys = (f x ,-_) $= appendNatural f xs ys

concatNatural : forall {X Y} (f : X -> Y) (xss : List (List X)) ->
                list f (concat xss) == concat (list (list f) xss)
concatNatural f [] = refl
concatNatural f (xs ,- xss) =
  list f (xs +L concat xss)
    =[ appendNatural f xs (concat xss) >=
  list f xs +L list f (concat xss)
    =[ (list f xs +L_) $= concatNatural f xss >=
  list f xs +L concat (list (list f) xss)
    [QED]



  appendNT : NaturalTransformation (Delta -Func- (LIST *Fun LIST) -Func- SETPair) LIST
  transform appendNT X (xs , ys) = xs +L ys
  natural appendNT f = ext \ { (xs , ys) -> appendNatural f xs ys }



  transform concatNT = \ _ -> concat
  natural concatNT = \ f -> ext (concatNatural f)

-}
