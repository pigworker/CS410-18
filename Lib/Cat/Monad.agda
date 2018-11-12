{-# OPTIONS --type-in-type --no-unicode #-}
{- OPTIONS --irrelevant-projections -}
module Lib.Cat.Monad where

open import Lib.Basics
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.NatTrans
open import Lib.Cat.Solver

module _ {Obj : Set}{Arr : Obj -> Obj -> Set}{C : Category Arr} where
  
  record Monad {ObjM : Obj -> Obj}
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
      }

  record MonadMorphism
    {ObjM : Obj -> Obj}{M : Functor C C ObjM}(MonadM : Monad M)
    {ObjN : Obj -> Obj}{N : Functor C C ObjN}(MonadN : Monad N)
    : Set
    where
      open Category C
      open Functor
      open NaturalTransformation
      open Monad
      field
        mMorph : NaturalTransformation M N
        .mMorphReturn : (X : Obj) ->
          (transform (returnNT MonadM) X -arr- transform mMorph X)
          == transform (returnNT MonadN) X
        .mMorphJoin : (X : Obj) ->
             (transform (joinNT MonadM) X -arr- transform mMorph X)
          ==
             (transform mMorph (ObjM X) -arr- map N (transform mMorph X)
                                      -arr- transform (joinNT MonadN) X)

  module _
    {ObjM : Obj -> Obj}{M : Functor C C ObjM}{MonadM : Monad M}
    {ObjN : Obj -> Obj}{N : Functor C C ObjN}{MonadN : Monad N}
    where
    open NaturalTransformation
    open MonadMorphism

    eqMonadMorph :
      (p q : MonadMorphism MonadM MonadN) ->
      ((X : Obj) -> transform (mMorph p) X == transform (mMorph q) X) ->
      p == q
    eqMonadMorph (record { mMorph = p }) (record { mMorph = q }) prf
      rewrite eqNatTrans p q prf = refl

  SomeMonad : Set
  SomeMonad = Sg (Obj -> Obj) \ ObjM ->
              Sg (Functor C C ObjM) \ M ->
              Monad M

  module _ where
    open Category C
    open Functor
    open NaturalTransformation
    open Monad
    open MonadMorphism

    MONAD : Category {SomeMonad} \ { (ObjM , M , MonadM) (ObjN , N , MonadN) ->
              MonadMorphism MonadM MonadN }
    mMorph (Category.idArr MONAD) = idNT
    mMorphReturn (Category.idArr MONAD) X = _-arr-idArr _
    mMorphJoin (Category.idArr MONAD {ObjM , M , MonadM}) X =
      [=IN C !
        (< transform (joinNT MonadM) X > -syn- idSyn)
          =[[ categories refl >>=
        (idSyn -syn- mapSyn M idSyn -syn- < transform (joinNT MonadM) X >)
          [[QED]]
      =]
    mMorph ((MONAD Category.-arr- mn) np) = mMorph mn -NT- mMorph np
    mMorphReturn (Category._-arr-_ MONAD {_ , _ , MonadM} {_ , _ , MonadN} {_ , _ , MonadP} mn np) X
      =
      [=IN C !
       (< transform (returnNT MonadM) X > -syn-
        < transform (mMorph mn) X > -syn- < transform (mMorph np) X >)
         =[[ categories refl >>=
       (-[ < transform (returnNT MonadM) X > -syn-
           < transform (mMorph mn) X > ]- -syn- < transform (mMorph np) X >)
         =[[ reduced ((rq (mMorphReturn mn X)) , rd) >>=
       (-[ < transform (returnNT MonadN) X > ]- -syn- < transform (mMorph np) X >)
         =[[ arrEq (mMorphReturn np X) >>=
       < transform (returnNT MonadP) X >
         [[QED]]
      =]
    mMorphJoin (Category._-arr-_ MONAD
                {ObjM , M , MonadM} {ObjN , N , MonadN} {ObjP , P , MonadP} mn np) X =
      [=IN C !
        (< transform (joinNT MonadM) X > -syn-
         < transform (mMorph mn) X > -syn- < transform (mMorph np) X >)
           =[[ categories refl >>=
        (-[ < transform (joinNT MonadM) X > -syn-
            < transform (mMorph mn) X > ]- -syn- < transform (mMorph np) X >)
           =[[ reduced (rq (mMorphJoin mn X) , rd) >>=
        (-[ < transform (mMorph mn) (ObjM X) > -syn-
            mapSyn N < transform (mMorph mn) X > -syn-
            < transform (joinNT MonadN) X > ]-
          -syn- < transform (mMorph np) X >)
           =[[ categories refl >>=
        (< transform (mMorph mn) (ObjM X) > -syn-
         mapSyn N < transform (mMorph mn) X > -syn-
         -[ < transform (joinNT MonadN) X > -syn- < transform (mMorph np) X > ]-)
           =[[ reduced (rd , rd , rq (mMorphJoin np X)) >>=
        (< transform (mMorph mn) (ObjM X) > -syn-
         mapSyn N < transform (mMorph mn) X > -syn-
         -[ < transform (mMorph np) (ObjN X) > -syn-
            mapSyn P < transform (mMorph np) X > -syn-
            < transform (joinNT MonadP) X > ]-)
           =[[ categories refl >>=
        (< transform (mMorph mn) (ObjM X) > -syn-
         -[ mapSyn N < transform (mMorph mn) X > -syn- < transform (mMorph np) (ObjN X) > ]- -syn-
            mapSyn P < transform (mMorph np) X > -syn-
            < transform (joinNT MonadP) X >)
           =<< reduced (rd , rq (natural (mMorph np) (transform (mMorph mn) X)) , rd , rd) ]]=
        (< transform (mMorph mn) (ObjM X) > -syn-
         -[ < transform (mMorph np) (ObjM X) > -syn- mapSyn P < transform (mMorph mn) X > ]- -syn-
            mapSyn P < transform (mMorph np) X > -syn-
            < transform (joinNT MonadP) X >)
           =[[ categories refl >>=
        ((< transform (mMorph mn) (ObjM X) > -syn- < transform (mMorph np) (ObjM X) >) -syn-
         mapSyn P (< transform (mMorph mn) X > -syn- < transform (mMorph np) X >) -syn-
         < transform (joinNT MonadP) X >)
         [[QED]]
      =]
    Category.idArr-arr- MONAD f = eqMonadMorph _ _ \ X -> idArr-arr- _
    Category._-arr-idArr MONAD f = eqMonadMorph _ _ \ X -> _ -arr-idArr
    Category.assoc-arr- MONAD f g h = eqMonadMorph _ _ \ X -> assoc-arr- _ _ _

  module _ where
    open Functor
    open MonadMorphism
    
    ForgetMONAD : Functor MONAD (FUNCTOR C C) \ { (ObjM , M , _) -> ObjM , M }
    map ForgetMONAD = mMorph
    mapidArr ForgetMONAD = refl
    map-arr- ForgetMONAD f g = refl

