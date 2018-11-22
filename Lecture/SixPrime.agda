{-# OPTIONS --type-in-type --no-unicode #-}
{-# OPTIONS --irrelevant-projections #-}
module Lecture.SixPrime where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.NatTrans
open import Lib.Cat.Adjunction
open import Lib.Cat.Monad
open import Lib.Cat.Solver

{-
module _ {ObjF : Set -> Set}(F : Functor SET SET ObjF) where

  open NaturalTransformation
  open MonadMorphism
  open Functor
  open Monad

  data M (X : Set) : Set where
    ret : X -> M X
    layer : ObjF (M X) -> M X

-- ObjF X = X -> X would make Agda allow programs that loop

-- ObjF X = (X -> Two) -> Two is a functor, but allowing this makes
--   the logic inconsistent with classical logic: it claims Pow (PowX) = X

  funM : Functor SET SET M
  map funM h (ret x) = ret (h x)
  map funM h (layer fx) = layer {!!}
  mapidArr funM = {!!}
  map-arr- funM = {!!}

  retM : NaturalTransformation (ID SET) funM
  transform retM X = ret
  natural retM = {!!}

  joinM : NaturalTransformation (funM -Func- funM) funM
  transform joinM X (ret mx) = mx
  transform joinM X (layer fx) = layer {!!}
  natural joinM = {!!}

  MonadM : Monad funM
  returnNT MonadM = retM
  joinNT MonadM = joinM
  returnJoin MonadM = {!!}
  mapReturnJoin MonadM = {!!}
  joinJoin MonadM = {!!}

  morph : {ObjN : Set -> Set}{N : Functor SET SET ObjN}(MonadN : Monad N)
          (f : NaturalTransformation F N) ->
          MonadMorphism MonadM MonadN
  transform (mMorph (morph MonadN f)) X (ret x) = transform (returnNT MonadN) X x
  transform (mMorph (morph MonadN f)) X (layer fx) = {!!}
  natural (mMorph (morph MonadN f)) k = {!!}
  mMorphReturn (morph MonadN f) X = refl
  mMorphJoin (morph MonadN f) = {!!}
-}

record Con{-tainer-} : Set where
  constructor _<!_
  field
    Sh{-ape-} : Set
    Po{-sition-} : Sh -> Set

[[_]]C : Con -> Set -> Set
[[ Sh <! Po ]]C X = Sg Sh \ s -> Po s -> X

map<! : {C : Con} -> {X Y : Set} -> (X -> Y) -> [[ C ]]C X -> [[ C ]]C Y
map<! f (s , g) = (s , (g - f))

[[_]]CF : (C : Con) -> Functor SET SET [[ C ]]C
Functor.map [[ C ]]CF = map<!
Functor.mapidArr [[ C ]]CF = refl
Functor.map-arr- [[ C ]]CF k l = refl

data M (C : Con)(X : Set) : Set where
  ret : X -> M C X
  layer : [[ C ]]C (M C X) -> M C X

join : {C : Con}{X : Set} -> M C (M C X) -> M C X
join (ret mx) = mx
join (layer (s , f)) = layer (s , (\ p -> join (f p)))


-- The category of container functors

CON : Category {Con} \ { C C' -> NaturalTransformation ([[ C ]]CF) ([[ C' ]]CF) }
Category.idArr CON = idNT
Category._-arr-_ CON = _-NT-_
Category.idArr-arr- CON f = refl
Category._-arr-idArr CON f = refl
Category.assoc-arr- CON f g h = refl



module _ {C : Con} where

  open Functor
  open Monad

  MC : Set -> Set
  MC = M C

  mapM : {X Y : Set} -> (X -> Y) -> MC X -> MC Y
  mapM f (ret x) = ret (f x)
  mapM f (layer (s , g)) = layer (s , (\ x -> mapM f (g x)))

  mapMid : {X : Set} -> (x : MC X) -> mapM id x == x
  mapMid (ret x) = refl
  mapMid (layer (s , g)) = (\ z → layer (s , z)) $= ext (\ x -> mapMid (g x))

  mapM-arr- : {X Y Z : Set}{f : X -> Y}{g : Y -> Z} ->
              (x : MC X) -> mapM (f - g) x == (mapM f - mapM g) x
  mapM-arr- (ret x) = refl
  mapM-arr- (layer (s , h)) = (\ z → layer (s , z))
                                       $= ext (\ x -> mapM-arr- (h x))

  joinNatural : {X Y : Set}(f : X -> Y) -> (x : M C (M C X)) ->
              mapM f (join x) == (join (mapM (mapM f) x))
  joinNatural f (ret x) = refl
  joinNatural f (layer (s , g)) = (\ z → layer (s , z))
                                      $= ext (\ x -> joinNatural f (g x))

  joinLaw2 : {X : Set}(x : M C X) -> join (mapM ret x) == x
  joinLaw2 (ret x) = refl
  joinLaw2 (layer (s , g)) = (\ z → layer (s , z))
                                  $= ext (\ x -> joinLaw2 (g x))

  joinLaw3 : {X : Set}(x : M C (M C (M C X))) ->
           join (join x) == join (mapM join x)
  joinLaw3 (ret x) = refl
  joinLaw3 (layer (s , g)) = (\ z → layer (s , z))
                                     $= ext (\ x -> joinLaw3 (g x))


module _ (C : Con) where

  open Functor
  open Monad
  open NaturalTransformation

  funM : Functor SET SET (M C)
  map funM = mapM
  mapidArr funM = ext mapMid
  map-arr- funM f g = ext mapM-arr-


  monadM : Monad funM
  transform (returnNT monadM) X = ret
  natural (returnNT monadM) f = refl
  transform (joinNT monadM) X = join
  natural (joinNT monadM) f = ext (joinNatural f)
  returnJoin monadM = refl
  mapReturnJoin monadM = ext joinLaw2
  joinJoin monadM = ext joinLaw3


module _ where

  open Functor
  open NaturalTransformation
  open MonadMorphism


  Mmap : forall {C C'} ->
         ((X : Set) -> [[ C ]]C X -> [[ C' ]]C X) ->
         (X : Set) -> M C X -> M C' X
  Mmap e X (ret x) = ret x
  Mmap e X (layer (s , g)) = layer (e _ (s , \ x -> Mmap e X (g x)))


  .Mmap-natural : forall {C C'} ->
                 (e : NaturalTransformation [[ C ]]CF [[ C' ]]CF) ->
                 {X Y : Set} (f : X -> Y) -> (x : M C X) ->
                 mapM f (Mmap (transform e) X x) == Mmap (transform e) Y (mapM f x)
  Mmap-natural e f (ret x) = refl
  Mmap-natural {C} {C'} e {X} {Y} f (layer (s , g)) = layer $= (
    (fst
      (transform e (M C' X) (s , (\ x -> Mmap (transform e) X (g x))))
      ,
    (snd (transform e (M C' X)
      (s , (\ x -> Mmap (transform e) X (g x)))) - (mapM f)))
        =[ refl >=
     (map<! (Mmap (transform e) X) - (transform e (M C' X) - map<! (mapM f))) (s , g)
        =[ (\ z -> z (s , g)) $=
        ([=IN SET !
          mapSyn [[ C ]]CF < Mmap (transform e) X > -syn-
          -[ < transform e (M C' X) > -syn-
          mapSyn [[ C' ]]CF < mapM f > ]-
            =[[ reduced (rd , rq (natural e (mapM f))) >>=
          mapSyn [[ C ]]CF < Mmap (transform e) X > -syn-
          -[ mapSyn [[ C ]]CF < mapM f > -syn-
             < transform e (M C' Y) > ]-
            =[[ categories refl >>=
          mapSyn [[ C ]]CF (< Mmap (transform e) X > -syn-
          < mapM f >) -syn- < transform e (M C' Y) > [[QED]] =])
        >=
     (map<! (Mmap (transform e) X - (mapM f)) - transform e (M C' Y)) (s , g)
        =[ (\ z → transform e (M C' Y) (s , z)) $= ext (\ x -> Mmap-natural e f (g x)) >=
     transform e (M C' Y) (s , (\ x -> Mmap (transform e) Y (mapM f (g x))))
        [QED])

  .mjLaw : forall {C C'}
             (e : NaturalTransformation [[ C ]]CF [[ C' ]]CF) {X}
             (x : M C (M C X)) ->
             Mmap (transform e) X (join x) == join (mapM (Mmap (transform e) X) (Mmap (transform e) (M C X) x))
  mjLaw e (ret x) = refl
  mjLaw {C} {C'} e {X} (layer (s , g)) = layer $= (
      (transform e (M C' X) (s , (\ x -> Mmap (transform e) X (join (g x)))))
      =[ (\ z -> transform e (M C' X) (s , z)) $= (ext \ x -> mjLaw e (g x)) >=
      (transform e (M C' X) (s , (\ x -> join (mapM (Mmap (transform e) X) (Mmap (transform e) (M C X) (g x))))))
      =[ refl >=
      (transform e (M C' X) (map<! (Mmap (transform e) (M C X) -arr- mapM (Mmap (transform e) X) -arr- join) (s , g)))
      =[ (\ z -> z (s , g)) $= [=IN SET !
         mapSyn [[ C ]]CF < Mmap (transform e) (M C X) > -syn- -[ mapSyn [[ C ]]CF (< mapM (Mmap (transform e) X) > -syn- < join >) -syn- < transform e (M C' X) > ]-
           =<< reduced (rd , rq (natural e (mapM (Mmap (transform e) X) - join ))) ]]=
         mapSyn [[ C ]]CF < Mmap (transform e) (M C X) > -syn- -[ < transform e (M C' (M C X)) > -syn- mapSyn [[ C' ]]CF < mapM (Mmap (transform e) X) - join > ]-
           =[[ categories refl >>=
         mapSyn [[ C ]]CF < Mmap (transform e) (M C X) > -syn- < transform e (M C' (M C X)) > -syn- mapSyn [[ C' ]]CF < mapM (Mmap (transform e) X) - join >
           [[QED]]
       =]
      >=
      map<! (mapM (Mmap (transform e) X) - join) (transform e (M C' (M C X)) (map<! (Mmap (transform e) (M C X)) (s , g)))
      =[ refl >=
      (fst (transform e (M C' (M C X)) (s , (g - Mmap (transform e) (M C X)))))
        ,
        (snd (transform e (M C' (M C X)) (s , (g - Mmap (transform e) (M C X)))) -arr- (mapM (Mmap (transform e) X) -arr- join))
      [QED]) where open Category SET

  monadMmap : forall {C C'} ->
                   NaturalTransformation [[ C ]]CF [[ C' ]]CF ->
                   MonadMorphism (monadM C) (monadM C')
  transform (mMorph (monadMmap e)) = Mmap (transform e)
  natural (mMorph (monadMmap e)) f = ext (Mmap-natural e f)
  mMorphReturn (monadMmap e) X = refl
  mMorphJoin (monadMmap e) X = ext (mjLaw e)

  Mmap-id : forall {C X} (x : M C X) ->
          Mmap (\ X -> id) X x == x
  Mmap-id (ret x) = refl
  Mmap-id (layer (s , g)) = (\ z -> layer (s , z)) $= ext (\ x -> Mmap-id (g x))

  .Mmap-arr : forall {C C' C''}
              {f : NaturalTransformation [[ C ]]CF   [[ C' ]]CF}
              {g : NaturalTransformation [[ C' ]]CF ([[ C'' ]]CF)}
              {X} (x : M C X) ->
              Mmap (\ X a -> transform g X (transform f X a)) X x
                                == Mmap (transform g) X (Mmap (transform f) X x)
  Mmap-arr (ret x) = refl
  Mmap-arr {C} {C'} {C''} {f} {g} {X} (layer (s , h)) = ((transform g (M C'' X)) - layer) $= (
    transform f (M C'' X) (s , (h - Mmap (\ X -> (transform f X) - transform g X) X))
         =[ (\ z -> transform f (M C'' X) (s , z)) $= ext (\ x -> Mmap-arr {f = f} {g} (h x)) >=
    transform f (M C'' X) (s , (h - (Mmap (transform f) X - Mmap (transform g) X)))
         =[ refl >=
    (map<! (Mmap (transform f) X - (Mmap (transform g) X)) - transform f (M C'' X)) (s , h)
         =[ ((\ z -> z (s , h)) $=
            ([=IN SET !
             mapSyn [[ C ]]CF (< Mmap (transform f) X >  -syn- < Mmap (transform g) X >) -syn- < transform f (M C'' X) >
               =[[ categories refl >>=
             mapSyn [[ C ]]CF < Mmap (transform f) X > -syn- -[ mapSyn [[ C ]]CF < Mmap (transform g) X > -syn- < transform f (M C'' X) > ]-
               =<< reduced (rd , rq (natural f (Mmap (transform g) X))) ]]=
             mapSyn [[ C ]]CF < Mmap (transform f) X > -syn- -[ < transform f (M C' X) > -syn- mapSyn [[ C' ]]CF < Mmap (transform g) X > ]-
             [[QED]]
             =]))
         >=
       map<! (Mmap (transform g) X) (transform f (M C' X) (map<! (Mmap (transform f) X) (s , h)))
         =[ refl >=
       fst (transform f (M C' X) (s , (h - Mmap (transform f) X))) ,
      (snd (transform f (M C' X) (s , (h - Mmap (transform f) X))) - Mmap (transform g) X)
        [QED])


  FREE : Functor CON MONAD \ { C -> _ , _ , monadM C }
  FREE = record { map = monadMmap
                ; mapidArr = eqMonadMorph _ _ \ X -> ext Mmap-id
                ; map-arr- = \ f g -> eqMonadMorph _ _ \ X -> ext (Mmap-arr {f = f} {g})
                }

module _ {C : Con}{ObjM' : Set -> Set}{M' : Functor SET SET ObjM'}{monadM' : Monad M'} where

  open Functor
  open NaturalTransformation
  open MonadMorphism
  open Monad

  lift : NaturalTransformation [[ C ]]CF M' -> (X : Set) -> M C X -> ObjM' X
  lift e X (ret x) = transform (returnNT monadM') X x
  lift e X (layer (s , f)) = transform (joinNT monadM') X (transform e (ObjM' X) (s , \ x -> lift e X (f x)))

  .lift-natural : {X Y : Set} ->
                 (e : NaturalTransformation [[ C ]]CF M') (f : X -> Y)(x : M C X) ->
                 map M' f (lift e X x) == lift e Y (mapM f x)
  lift-natural e f (ret x) = (\ z -> z x) $= natural (returnNT monadM') f
  lift-natural {X} {Y} e f (layer (s , g)) =
    _ =[ lemma s g >= (\ z → transform (joinNT monadM') Y (transform e (ObjM' Y) (s , z))) $= ext \ x -> lift-natural e f (g x)
    where lemma : {X Y : Set}{f : X -> Y}(s : Con.Sh C)(g : Con.Po C s -> M C X) ->
                 map M' f (transform (joinNT monadM') X (transform e (ObjM' X) (s , (g - lift e X))))
                  ==
                 transform (joinNT monadM') Y (transform e (ObjM' Y) (s , (\ a -> map M' f (lift e X (g a)))))
          lemma {X} {Y} {f} s g = (\ z -> z (s , g)) $=
            [=IN SET !
            mapSyn [[ C ]]CF < lift e X > -syn- < transform e (ObjM' X) > -syn- -[ < transform (joinNT monadM') X > -syn- mapSyn M' < f > ]-
              =[[ reduced (rd , (rd , (rq (natural (joinNT monadM') f)))) >>=
            mapSyn [[ C ]]CF < lift e X > -syn- < transform e (ObjM' X) > -syn- -[ mapSyn M' (mapSyn M' < f >) -syn- < transform (joinNT monadM') Y > ]-
              =[[ categories refl >>=
            mapSyn [[ C ]]CF < lift e X > -syn- -[ < transform e (ObjM' X) > -syn- mapSyn M' (mapSyn M' < f >) ]- -syn- < transform (joinNT monadM') Y >
              =[[ reduced (rd , (rq (natural e (map M' f)) , rd)) >>=
            mapSyn [[ C ]]CF < lift e X > -syn- -[ mapSyn [[ C ]]CF (mapSyn M' < f >) -syn- < transform e (ObjM' Y) > ]- -syn- < transform (joinNT monadM') Y >
              =[[ categories refl >>=
            -[ mapSyn [[ C ]]CF < lift e X > -syn- mapSyn [[ C ]]CF (mapSyn M' < f >) ]- -syn- < transform e (ObjM' Y) > -syn- < transform (joinNT monadM') Y >
              [[QED]]
            =]

  .lift-morphJoin : (e : NaturalTransformation [[ C ]]CF M') {X : Set}
                   (x : M C (M C X)) ->
                   lift e X (join x) ==
                     transform (joinNT monadM') X (map M' (lift e X) (lift e (M C X) x))
  lift-morphJoin e {X} (ret x) = (\ z -> z x) $= ([=IN SET !
    < lift e X > -syn- idSyn
       =<< reduced (rd , rq (returnJoin monadM' {X})) ]]=
    < lift e X > -syn- -[ < transform (returnNT monadM') (ObjM' X) > ]- -syn- < transform (joinNT monadM') X >
      =[[ categories refl >>=
    -[ < lift e X > -syn- < transform (returnNT monadM') (ObjM' X) > ]- -syn- < transform (joinNT monadM') X >
      =<< reduced (rq (natural (returnNT monadM') (lift e X)) , rd) ]]=
    -[ < transform (returnNT monadM') (M C X) > -syn- mapSyn M'  < lift e X > ]- -syn- < transform (joinNT monadM') X >
      [[QED]]
    =])
  lift-morphJoin e {X} (layer (s , g)) =
    _ =[ (\ z -> transform (joinNT monadM') X (transform e (ObjM' X) (s , z))) $= ext (\ x -> lift-morphJoin e (g x)) >= (\ z -> z (s , g)) $=
    ([=IN SET !
      mapSyn [[ C ]]CF (< lift e (M C X) > -syn- mapSyn M' < lift e X > -syn- < transform (joinNT monadM') X >)  -syn- < transform e (ObjM' X) > -syn- < transform (joinNT monadM') X >
        =[[ categories refl >>=
      mapSyn [[ C ]]CF < lift e (M C X) > -syn- mapSyn [[ C ]]CF (mapSyn M' < lift e X > ) -syn- -[ mapSyn [[ C ]]CF (< transform (joinNT monadM') X >) -syn- < transform e (ObjM' X) > ]- -syn- < transform (joinNT monadM') X >
        =<< reduced (rd , rd , rq (natural e (transform (joinNT monadM') X)) , rd) ]]=
      mapSyn [[ C ]]CF < lift e (M C X) > -syn- mapSyn [[ C ]]CF (mapSyn M' < lift e X >) -syn- -[ < transform e (ObjM' (ObjM' X)) > -syn- mapSyn M' < transform (joinNT monadM') X > ]- -syn- < transform (joinNT monadM') X >
        =[[ categories refl >>=
      mapSyn [[ C ]]CF < lift e (M C X) > -syn- mapSyn [[ C ]]CF (mapSyn M' < lift e X >) -syn- < transform e (ObjM' (ObjM' X)) > -syn- -[ mapSyn M' < transform (joinNT monadM') X > -syn- < transform (joinNT monadM') X > ]-
        =<< reduced (rd , rd , rd , rq (joinJoin monadM')) ]]=
      mapSyn [[ C ]]CF < lift e (M C X) > -syn- mapSyn [[ C ]]CF (mapSyn M' < lift e X >) -syn- < transform e (ObjM' (ObjM' X)) > -syn- -[ < transform (joinNT monadM') (ObjM' X) > -syn- < transform (joinNT monadM') X > ]-
        =[[ categories refl >>=
      mapSyn [[ C ]]CF < lift e (M C X) > -syn- -[ mapSyn [[ C ]]CF (mapSyn M' < lift e X >) -syn- < transform e (ObjM' (ObjM' X)) > ]- -syn- < transform (joinNT monadM') (ObjM' X) > -syn- < transform (joinNT monadM') X >
        =<< reduced (rd , rq (natural e (map M' (lift e X))) , rd , rd) ]]=
      mapSyn [[ C ]]CF < lift e (M C X) > -syn- -[ < transform e (ObjM' (M C X)) > -syn- mapSyn M' (mapSyn M' < lift e X >) ]- -syn- < transform (joinNT monadM') (ObjM' X) > -syn- < transform (joinNT monadM') X >
        =[[ categories refl >>=
      mapSyn [[ C ]]CF < lift e (M C X) > -syn- < transform e (ObjM' (M C X)) > -syn- -[ mapSyn M' (mapSyn M' < lift e X >) -syn- < transform (joinNT monadM') (ObjM' X) > ]- -syn- < transform (joinNT monadM') X >
        =<< reduced (rd , rd , (rq (natural (joinNT monadM') (lift e X))) , rd) ]]=
      mapSyn [[ C ]]CF < lift e (M C X) > -syn- < transform e (ObjM' (M C X)) > -syn- -[ < transform (joinNT monadM') (M C X) >
        -syn- mapSyn M' < lift e X > ]- -syn- < transform (joinNT monadM') X >
        [[QED]]
      =])

  liftMor : NaturalTransformation [[ C ]]CF M' ->  MonadMorphism  (monadM C) monadM'
  transform (mMorph (liftMor e)) = lift e
  natural (mMorph (liftMor e)) f = ext (lift-natural e f)
  mMorphReturn (liftMor e) X = refl
  mMorphJoin (liftMor e) X = ext (lift-morphJoin e)

  dropMor : MonadMorphism  (monadM C) monadM' -> NaturalTransformation [[ C ]]CF M'
  transform (dropMor e) X y = transform (mMorph e) X (layer (map<! ret y))
  natural (dropMor e) f = ext lemma
    where lemma : {X Y : Set} {f : X -> Y} (x : [[ C ]]C X) ->
                  map M' f (transform (mMorph e) X (layer (fst x , (\ a -> ret (snd x a)))))
                     == transform (mMorph e) Y (layer (fst x , (\ a -> ret (f (snd x a)))))
          lemma {X = X} {Y} {f} (s , g) = (\ z -> (z (s , g))) $= (
            [=IN SET !
            mapSyn [[ C ]]CF < ret > -syn- < layer > -syn- -[ < transform (mMorph e) X > -syn- mapSyn M' < f > ]-
              =[[ reduced (rd , (rd , (rq (natural (mMorph e) f)))) >>=
            mapSyn [[ C ]]CF < ret > -syn- < layer > -syn- -[ mapSyn (funM C) < f > -syn- < transform (mMorph e) Y > ]-
              =[[ categories refl >>=
            -[ mapSyn [[ C ]]CF < ret > -syn- < layer > -syn-  mapSyn (funM C) < f > ]- -syn- < transform (mMorph e) Y >
              =[[ reduced (rq refl , rd) >>=
            -[ mapSyn [[ C ]]CF (< f > -syn- < ret >) -syn- < layer > ]- -syn- < transform (mMorph e) Y >
              =[[ categories refl >>=
            mapSyn [[ C ]]CF (< f > -syn- < ret >) -syn- < layer > -syn- < transform (mMorph e) Y >
              [[QED]]
            =])



  .roundtrip1 : (e : MonadMorphism  (monadM C) monadM') ->
               liftMor (dropMor e) == e
  roundtrip1 e = eqMonadMorph _ _ \ X -> ext (lemma X)
   where lemma : forall X -> (x : M C X) ->
                  lift (dropMor e) X x == transform (mMorph e) X x
         lemma X (ret x) = sym ((\ z -> z x) $= mMorphReturn e X)
         lemma X (layer (s , g)) = let join' = transform (joinNT monadM')
                                       return' = transform (returnNT monadM')
                                       eta =  transform (mMorph e) in
           join' X (eta (ObjM' X) (layer (map<! ((lift (dropMor e) X) - ret) (s , g))))
             =[ (\ z -> join' X (eta (ObjM' X) (layer (s , z))))
                            $= ext (\ x -> ret $= lemma X (g x)) >=
           join' X (eta (ObjM' X) (layer (map<! (eta X - ret) (s , g))))
             =[ (\ z -> join' X (z (s , g))) $= sym (natural (dropMor e) (eta X)) >=
           join' X (map M' (eta X) (eta (M C X) (layer (map<! ret (s , g)))))
             =< (\ z -> z (layer (map<! ret (s , g)))) $= mMorphJoin e X ]=
           eta X (join (layer (map<! ret (s , g))))
             =< (\ z -> eta X (layer (s , z))) $= ext (\ x -> joinLaw2 (g x)) ]=
           eta X (join (mapM ret (layer (s , g))))
             =[ (eta X) $= joinLaw2 (layer (s , g)) >=
           eta X (layer (s , g))
             [QED]

  .roundtrip2 : (e : NaturalTransformation [[ C ]]CF M') ->
                dropMor (liftMor e) == e
  roundtrip2 e = eqNatTrans _ _ \ X -> ext (lemma X)
    where lemma : forall X y ->
                  transform (joinNT monadM') X
                    (transform e (ObjM' X)
                      (map<! (transform (returnNT monadM') X) y))
                     == transform e X y
          lemma X y = let join' = transform (joinNT monadM')
                          return' = transform (returnNT monadM')
                          eta = transform e in
             join' X (eta (ObjM' X) (map<! (return' X) y))
               =< (\ z -> join' X (z y)) $= natural e (return' X) ]=
             join' X (map M' (return' X) (eta X y))
               =[ (\ z -> z (eta X y)) $= (mapReturnJoin monadM') >=
             eta X y
               [QED]







-- M C as a container itself:

data MSh (C : Con) : Set where
  retS : MSh C
  wrapS : (s : Con.Sh C) -> (Con.Po C s -> MSh C) -> MSh C

MPo : (C : Con) -> MSh C -> Set
MPo C retS = One
MPo C (wrapS s f) = Sg (Con.Po C s) \ p -> MPo C (f p)

MCon : (C : Con) -> Set -> Set
MCon C = [[ MSh C <! MPo C ]]C

ret' : {C : Con}{X : Set} -> X -> MCon C X
ret' x = retS  , \ tt -> x

layer' : {C : Con}{X : Set} -> [[ C ]]C (MCon C X) -> MCon C X
layer' (s , f) = wrapS s (f - fst) , \ { (p , x) -> snd (f p) x }

oneWay : {C : Con}{X : Set} -> M C X -> MCon C X
oneWay (ret x) = ret' x
oneWay (layer (s , g)) = layer' (s , \ x -> oneWay (g x))

otherWay : {C : Con}{X : Set} -> MCon C X -> M C X
otherWay (s , f) = otherWay' s f
  -- making the termination checker happy by avoiding Sigma types
  where otherWay' : {C : Con}{X : Set} -> (s : MSh C) -> (MPo C s -> X) -> M C X
        otherWay' retS  f = ret (f _)
        otherWay' (wrapS s g) f = layer (s , \ p -> otherWay' (g p) (\ z -> f (p , z)))



MonadCONT : Category {Sg Con \ C -> Monad [[ C ]]CF}
                     \ { (C , monadC) (C' , monadC') -> MonadMorphism monadC monadC' }
Category.idArr MonadCONT = Category.idArr MONAD
Category._-arr-_ MonadCONT = Category._-arr-_ MONAD
Category.idArr-arr- MonadCONT = Category.idArr-arr- MONAD
Category._-arr-idArr MonadCONT = Category._-arr-idArr MONAD
Category.assoc-arr- MonadCONT = Category.assoc-arr- MONAD

forgetMonad : Functor MonadCONT CON \ { (C , M) -> C }
forgetMonad = record { map = MonadMorphism.mMorph
                     ; mapidArr = refl
                     ; map-arr- = \ f g -> refl
                     }
