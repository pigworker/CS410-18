module Lib.Display where

open import Lib.Basics
open import Lib.Nat
open import Lib.Vec
open import Lib.Indexed

----------------------------------------------------------------------------
-- chars and strings
----------------------------------------------------------------------------

postulate       -- this means that we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING String #-}

primitive       -- these are baked in; they even work!
  primCharEquality    : Char -> Char -> Two
  primStringAppend    : String -> String -> String
  primStringToList    : String -> List Char
  primStringFromList  : List Char -> String


---------------------------------------------------------------------------
-- COLOURS
---------------------------------------------------------------------------

-- We're going to be making displays from coloured text.

data Colour : Set where
  black red green yellow blue magenta cyan white : Colour
{-# COMPILE GHC Colour = data HaskellSetup.Colour (HaskellSetup.Black | HaskellSetup.Red | HaskellSetup.Green | HaskellSetup.Yellow | HaskellSetup.Blue | HaskellSetup.Magenta | HaskellSetup.Cyan | HaskellSetup.White) #-}

record _**_ (S T : Set) : Set where
  constructor _,_
  field
    outl : S
    outr : T
open _**_
{-# COMPILE GHC _**_ = data (,) ((,)) #-}
infixr 4 _**_

{- Here's the characterization of keys I give you -}
data Direction : Set where up down left right : Direction
data Modifier : Set where normal shift control : Modifier
data Key : Set where
  char       : Char -> Key
  arrow      : Modifier -> Direction -> Key
  enter      : Key
  backspace  : Key
  delete     : Key
  escape     : Key
  tab        : Key
data Event : Set where
  key     : (k : Key) -> Event
  resize  : (w h : Nat) -> Event

{- This type collects the things you're allowed to do with the text window. -}
data Action : Set where
  goRowCol : Nat -> Nat -> Action    -- send the cursor somewhere
  sendText : List Char -> Action     -- send some text
  move     : Direction -> Nat -> Action  -- which way and how much
  fgText   : Colour -> Action
  bgText   : Colour -> Action

{- I wire all of that stuff up to its Haskell counterpart. -}
{-# FOREIGN GHC import qualified Lib.ANSIEscapes as ANSIEscapes #-}
{-# FOREIGN GHC import qualified Lib.HaskellSetup as HaskellSetup #-}
{-# COMPILE GHC Direction = data ANSIEscapes.Dir (ANSIEscapes.DU | ANSIEscapes.DD | ANSIEscapes.DL | ANSIEscapes.DR) #-}
{-# COMPILE GHC Modifier = data HaskellSetup.Modifier (HaskellSetup.Normal | HaskellSetup.Shift | HaskellSetup.Control) #-}
{-# COMPILE GHC Key = data HaskellSetup.Key (HaskellSetup.Char | HaskellSetup.Arrow | HaskellSetup.Enter | HaskellSetup.Backspace | HaskellSetup.Delete | HaskellSetup.Escape | HaskellSetup.Tab) #-}
{-# COMPILE GHC Event = data HaskellSetup.Event (HaskellSetup.Key | HaskellSetup.Resize) #-}
{-# COMPILE GHC Action = data HaskellSetup.Action (HaskellSetup.GoRowCol | HaskellSetup.SendText | HaskellSetup.Move | HaskellSetup.FgText | HaskellSetup.BgText) #-}

data ColourChar : Set where
  _-_#_ : (fg : Colour)(c : Char)(bg : Colour) -> ColourChar

paintAction : {wh : Nat * Nat} -> Matrix ColourChar wh -> List Action
paintAction = vecFoldR (vecFoldR (\ {(f - c # b) k -> \ as ->
  fgText f ,- bgText b ,- sendText (c ,- []) ,- k as}) id) []


postulate       -- Haskell has a monad for doing IO, which we use at the top level
  IO      : Set -> Set
  return  : {A : Set} -> A -> IO A
  _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
infixl 1 _>>=_
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}
{-# COMPILE GHC return = (\ _ -> return) #-}
{-# COMPILE GHC _>>=_ = (\ _ _ -> (>>=)) #-}


---------------------------------------------------------------------------
-- APPLICATIONS                                                          --
---------------------------------------------------------------------------

-- Here's a general idea of what it means to be an "application".
-- You need to choose some sort of size-dependent state, then provide these
-- bits and pieces. We need to know how the state is updated according to
-- events, with resizing potentially affecting the state's type. We must
-- be able to paint the state. The state should propose a cursor position.
-- (Keen students may modify this definition to ensure the cursor must be
-- within the bounds of the application.)

record Interface (Status : Set) : Set1 where
  constructor interface
  field
    Command  : Status -> Set     -- a.k.a. precondition
    Response : (before : Status)(command : Command before)
              -> Status -> Set  -- a.k.a. postcondition
open Interface public

record Server
  {Status   : Set}
  (Intf     : Interface Status)
  (Display  : Status -> Set)     -- a.k.a. invariant
  (now      : Status)
  : Set
  where
    coinductive
    field
      display : Display now
      react   : (command : Command Intf now) ->
                Sg Status \ next ->
                Response Intf now command next *
                Server Intf Display next
open Server public

AppInterface : Interface (Nat * Nat)
Command  AppInterface wh = Event
Response AppInterface whb (key k)      wha = wha == whb
Response AppInterface whb (resize w h) wha = wha == (w , h)

CursorPosition : Nat * Nat -> Set
CursorPosition wh = Nat * Nat

Application : Nat * Nat -> Set
Application = Server AppInterface
         (   Matrix ColourChar  -- what's on the screen?
         :*: CursorPosition     -- where's the cursor?
         )

TopLevel : Set
TopLevel = Sg (Nat * Nat) Application

appPaint : TopLevel -> List Action
appPaint (_ , app) =
  goRowCol 0 0 ,- paintAction p
     -- must have composition here, to work around compiler bug
     -- paintAction (paintMatrix p)
     -- segfaults, because p is erased
  +L (goRowCol (snd xy) (fst xy) ,- [])
  where
    pxy = display app
    p = fst pxy
    xy = snd pxy

appHandler : Event -> TopLevel -> TopLevel ** List Action
appHandler e (wh , app) with react app e
... | wh' , _ , app' = (_ , app') , appPaint (_ , app')

{- This is the bit of code I wrote in Haskell to animate your code. -}
postulate
  mainAppLoop : {S : Set} ->             -- program state
    -- INITIALIZER
    S ->                              -- initial state
    -- EVENT HANDLER
    (Event -> S ->                    -- event and state in
     S ** List Action) ->              -- new state and screen actions out
    -- PUT 'EM TOGETHER AND YOU'VE GOT AN APPLICATION!
    IO One
{-# COMPILE GHC mainAppLoop = (\ _ -> HaskellSetup.mainAppLoop) #-}

appMain : (forall wh -> Application wh) -> IO One
appMain app = mainAppLoop ((0 , 0) , app (0 , 0)) appHandler
  -- will get resized dynamically to size of terminal, first thing
