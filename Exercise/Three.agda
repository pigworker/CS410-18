{-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Exercise.Three where

open import Lib.Basics
open import Lib.Nat
open import Lib.Display         -- worth having a look at this
open import Lib.Indexed         -- you remember this, right?
open import Lib.Cat.Category
open import Lib.Cat.Functor
open import Lib.Cat.NatTrans
open import Lib.Cat.Monad
open import Lib.Cat.Adjunction
open import Lib.Vec             -- look here, too

open import Exercise.One
open import Exercise.Two


------------------------------------------------------------------------------
--  A Very Simple Application
------------------------------------------------------------------------------

-- By way of getting you started, we give you a very simple
-- application.  If you make sure all the holes are commented out, you
-- should be able to run this now! All it does is fill the terminal
-- with a given character (Ctrl-C quits). See the very bottom of this
-- file for instructions how to compile and run the program.

-- You can look up the definition of the type Application in
-- Lib.Display, or you can try to get the gist of it from this example
-- application. It's written in "copattern" style, showing how the
-- application discharges its obligations to produce behaviour on
-- demand.

rectApp : Char             -- character to display
       -> [ Application ]  -- an application of *any* screen size

-- To "display", an application must supply a pair of things:
fst (display (rectApp c wh))          -- a matrix of coloured characters
  = vPure (vPure (green - c # black))    -- here, copies of character c
snd (display (rectApp c wh))          -- the cursor position
  = wh -- the bottom right corner

-- To "react", an application must respond to events, which means giving
-- three things: (i) a new size, (ii) a proof that the new size is correct,
-- (iii) the new incarnation of the application.
-- What's the correct size?

--  When a key is pressed, the screen size must stay the same!
react (rectApp _ wh) (key (char c))  -- a printable character was typed, so
  = wh , refl , rectApp c wh  -- *preserve* screen size, switch to typed char
react (rectApp c wh) (key _)  -- another key was pressed, so
  = wh , refl , rectApp c wh  -- do nothing

--  When a resize happens, the screen size must become the demanded size!
react (rectApp c wh) (resize w h)
  = (w , h) , refl , rectApp c (w , h)


------------------------------------------------------------------------------
--  Applicative Functors (remember these from Haskell?)
------------------------------------------------------------------------------

-- We will have use of applicative functors in the building of applications.

record Applicative (F : Set -> Set) : Set where
  field
    pure  : forall {X} -> X -> F X
    _<*>_ : forall {X Y} -> F (X -> Y) -> F X -> F Y
  infixl 60 _<*>_
    -- We ought to demand the laws.
    -- You have enough to do, already.


{-mango UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
--  Vector Machinery
------------------------------------------------------------------------------

-- We're going to be working with matrices, i.e., vectors of vectors,
-- seen as a column of rows.

-- We will need some apparatus. Much has been built in lectures, so you might
-- want to forage for useful components.

-- ??? 3.1
-- Show that vectors of any given length are a functor on SET.

VEC : (n : Nat) -> Functor SET SET (\ X -> Vec X n)
VEC n = {!!}

-- ??? 3.2
-- Find the components to make vectors applicative, by pointwise application.

VApp : forall n -> Applicative \ X -> Vec X n
VApp n = {!!}

-- ??? 3.3
-- Show that vectors respect One and * on types.

void : forall {n : Nat} -> One -> Vec One n
void <> = {!!}

zip : forall {n S T} -> Vec S n * Vec T n -> Vec (S * T) n
zip (ss , ts) = {!!}


------------------------------------------------------------------------------
--  Pasting Algebras (for Vectors)
------------------------------------------------------------------------------

open _<|_  -- from Exercise.Two

-- A notion of "cutting" induces a functor.
-- The corresponding algebras are "pasting" operators.

Pasting : forall {I}(C : I <| I)(X : I -> Set) -> Set
Pasting C X = [ [[ C ]]Cr X -:> X ]

-- ??? 3.4
-- Find the component that gives vectors a pasting operator for NatCut
-- from Exercise.Two.

vecPaste : forall {X} -> Pasting NatCut (Vec X)
vecPaste = {!!}

END OF COMMENT mango-}


{-starfruit UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
--  Cutting in Multiple Dimensions
------------------------------------------------------------------------------

-- If we know how to cut up numbers (seen as lengths), we ought to be able
-- to cut up pairs of numbers (see as the width and height of a rectangle).

-- Let's approach the problem in small steps.

-- ??? 3.5
-- Angelic choice of cutting. (Here "angelic" means *you* get to choose which
-- sort of cut to make.)

_>+<_ : forall {O I} -> O <| I -> O <| I -> O <| I

-- Specification:
-- (i)   We get two different schemes for cutting the same sort of "outer"
--       into "inner" pieces.
-- (ii)  Combine them by offering to cut in accordance with either scheme.
-- (iii) The pieces should then be those given for the chosen cut in the
--       chosen scheme.

C >+< D = {!!}

-- ??? 3.6
-- Right and Left Framing

_>|_ : forall {O I}      (C : O <| I) J   ->      (O * J) <|     (I * J)
_|<_ : forall {O I}    J (C : O <| I)     ->  (J * O)     <| (J * I)

-- Specification:
-- These operators should generate higher dimensional cutting schemes
-- from some lower dimensional C,
-- by attaching an extra dimension, J,
-- which is never affected by a cut.
-- That is, the given value in O should determine the choice of cuts
-- according to C. All pieces should inherit the given value in J.

C >| J = {!!}
J |< C = {!!}

-- Intuition:
-- If you know how to cut up a number into parts, then you know how to
-- cut up a rectangle whose width is that number into subrectangles
-- whose widths are the parts. The height of the original rectangle
-- is then the height of all of its parts.

-- ??? 3.6
-- Combining Separate Dimensions

_|+|_ : forall {I J} -> I <| I -> J <| J -> (I * J) <| (I * J)

-- Specification:
-- (i)   We have two separate dimensions, indexed by I and J, respectively.
-- (ii)  We know, separately, a scheme for cutting each dimension.
-- (iii) We want a cutting scheme which allows us
--         either to cut the I dimension, preserving the J index,
--         or     to cut the J dimension, preserving the I index.

C |+| D = {!!}

-- Hint: use framing and angelic choice, of course!

-- By return of post, you obtain the scheme for cutting up rectangles
-- with axis-aligned cuts, either somewhere along their width or
-- somewhere along their height.

RectCut : (Nat * Nat) <| (Nat * Nat)
RectCut = NatCut |+| NatCut


------------------------------------------------------------------------------
--  Interlude: Euclid in Space (with a bit of Fibonacci)
------------------------------------------------------------------------------

-- This is by way of consolidating intuition about what is going on.

-- We can define the type of rectangular things which are actually square.

data Square : Nat * Nat -> Set where
  square : (n : Nat) -> Square (n , n)

-- See? You can't make a Square (w , h) unless w and h are equal.

-- ??? 3.7
-- Tile a rectangular area with square pieces.

example : Tree RectCut Square (13 , 8)

-- Specification:
-- (i)   If your current goal has equal width and height, give a square leaf.
-- (ii)  Otherwise, cut your rectangle into two pieces, the first of which
--       is square.

example = {!!}

-- Historical note:
-- This is exactly Euclid's algorithm for computing the greatest common
-- divisor of two numbers. The side-length of the square you stop with is
-- the g.c.d.! If you run Euclid's algorithm on a pair of consecutive
-- Fibonacci numbers (e.g., 13 and 8), you will find that you cut in
-- alternating dimensions until you get down to a square of side 1.

END OF COMMENT starfruit-}


{-lemon UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
--  Useful Structure for All
------------------------------------------------------------------------------

-- Given that Tree (the type for "cutting and cutting again" from
-- Exercise.Two) relies on the All construct, we need machinery for it.
-- We previously asked you to show its functoriality (the "all"
-- operator), but now we need a little more.

-- We will often find ourselves working with data in types like
--   All P (list f xs)              -- also known as  (list f - All P) xs
-- which is not the same type as
--   All (\ x -> P (f x)) xs        -- also known as  All (f - P) xs
-- The extra "list" is using f to reindex the elements of the list,
-- before we apply All P, but we can just as well compose f with P!

-- Moreover, any old
--   All P xs
-- can be seen as an
--   All P (list id xs)
-- because you know that list is a functorial action.

-- Have the following proof, on the house!

listId : forall {X}(xs : List X) -> list id xs == id xs
listId []        = refl
listId (x ,- xs) = (x ,-_) $= listId xs


-- ??? 3.8
-- Extend "all" to allow reindexing.

allExt : forall {X I J}                 -- some index types
     {P : I -> Set}{Q : J -> Set}       -- we shall turn Ps into Qs

     (f : X -> I)                       -- we shall reindex P by f
     {lf : List X -> List I}            -- we have a copy of list f
     (lfEq : forall xs -> list f xs == lf xs)

     (g : X -> J)                       -- we shall reindex Q by g
     {lg : List X -> List J}            -- we have a copy of list g
     (lgEq : forall xs -> list g xs == lg xs)

  -> [      (f - P) -:>      (g - Q) ]  -- we can turn Ps into Qs, so
  -> [ (lf - All P) -:> (lg - All Q) ]  -- turn (All P)s into (All Q)s!

-- We suggest the first move, but leave the rest to you.
allExt f {lf} lfEq g {lg} lgEq pq xs ps with lf xs | lfEq xs | lg xs | lgEq xs
allExt f {lf} lfEq g {lg} lgEq pq xs ps | ._ | refl | ._ | refl = {!!}

-- ??? 3.9 Reindexing
module _ {X Y}(f : X -> Y){P : Y -> Set} where

-- Check that you can define the following "identity functions"
-- by instantiating allExt appropriately.

  allList : [ All (f - P) -:> (list f - All P) ]
  allTsil : [ (list f - All P) -:> All (f - P) ]

  allList = allExt {!!} {!!} {!!} {!!} {!!}
  allTsil = allExt {!!} {!!} {!!} {!!} {!!}


-- ??? 3.10
-- Show that you can yank applicative structure out through All.

module _ {F : Set -> Set}(ApF : Applicative F) where
  open Applicative ApF

  allYank : forall {X}{P : X -> Set} ->
            [ All (P - F) -:> (All P - F) ]
  allYank fps = {!!}

-- Hint: this is a lot like "traverse" for All


-- ??? 3.11
-- Find the *indexed* applicative structure for All.

-- Just like vectors (which are indexed containers of unindexed data),
-- All has a kind of applicative structure, only for indexed data.

pureAll : forall {I}{P : I -> Set}
       -> [ P ] -> [ All P ]
appAll  : forall {I}{P Q : I -> Set}
       -> [ All (P -:> Q) -:> All P -:> All Q ]

pureAll p is = {!!}

appAll is pqs ps = {!!}

-- Hint: follow the recipe from Lib.Vec.


-- ??? 3.12
-- Implement transposition.

transpose : forall {I J}        -- You have two index types...
     {_~_ : I -> J -> Set}      -- and a relation between.
     {is : List I}{js : List J} -- You have a list of indices in each.
  -> All (\ i -> All (i ~_) js) is  -- Every i is related to every j.
  -> All (\ j -> All (_~ j) is) js  -- Show every j is related to every i.

transpose xss = {!!}

-- Hints:
-- (i)  This is a classic exercise in deploying applicative structure.
-- (ii) We're asking you to build this because we think you will need it.


-- ??? 3.13
-- Use applicative structure to combine pasting algebras for multiple
-- dimensions.

compPaste : forall {I J}                -- What you get:
  -> (C : I <| I)(F : Set -> I -> Set)  -- C cuts correspond to F layers

  -> (D : J <| J)(G : Set -> J -> Set)  -- D cuts correspond to G layers
  -> (forall j -> Applicative \ X -> G X j)  -- and G is always applicative

  -> (forall {X} -> Pasting C (F X))    -- polymorphic C-paster for F
  -> (forall {X} -> Pasting D (G X))    -- polymorphic D-paster for G
                                        -- What we want:
  -> (forall {X} -> Pasting (C |+| D) \ { (i , j) -> G (F X i) j})
     -- a polymorphic two-dimensional paster for Gs of Fs

compPaste C F D G ApG cf dg (i , j) (cut , ps) = {!!}


-- Now that you've done some hard training, you can do some actual karate!

-- ??? 3.14
-- In one line, give a RectCut-paster for Matrix (from Lib.Vec)

matPaste : forall {X} -> Pasting RectCut (Matrix X)
matPaste = {!!}


-- ??? 3.15
-- In one line, show how to paste together a Matrix from a tree whose
-- leaves each map to a Matrix.

treeMatrix : forall {X P} ->
  [ P -:> Matrix X ] -> [ Tree RectCut P -:> Matrix X ]
treeMatrix l = {!!}


------------------------------------------------------------------------------
--  Seeing the Matrix (have a break; check your work)
------------------------------------------------------------------------------

-- We'll do this bit, except for the equation to check at the end.

-- Here's a function to draw an ascii-art square of a given size.
squareChar : [ Square -:> Matrix Char ]
squareChar _ (square zero)          = []
squareChar _ (square (suc zero))    = ('#' ,- []) ,- []
squareChar _ (square (suc (suc i))) rewrite comm+N 1 i
  =  (',' ,- vPure '-' +V '.' ,- [])         --   ,-.
  ,- vPure ('|' ,- vPure ' ' +V '|' ,- [])   --   | |
  +V ('`' ,- vPure '-' +V '\'' ,- [])        --   `-'
  ,- []

-- You can flatten a matrix of characters to a list of strings.
showMatrix : forall {wh} -> Matrix Char wh -> List String
showMatrix = vecFoldR _,-_ [] - list (vecFoldR _,-_ [] - primStringFromList)

-- Let's get the matrix from your earlier example Tree of Squares.
exampleMatrix : Matrix Char (13 , 8)
exampleMatrix = treeMatrix squareChar (13 , 8) example

-- It should look like this.
expectedOutput : List String
expectedOutput =
  ",------.,---." ,-
  "|      ||   |" ,-
  "|      ||   |" ,-
  "|      ||   |" ,-
  "|      |`---'" ,-
  "|      |,-.,." ,-
  "|      || |`'" ,-
  "`------'`-'##" ,-
  []

-- Does it?
checkOutput : showMatrix exampleMatrix == expectedOutput
checkOutput = {!!}

END OF COMMENT lemon-}


{-olive UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
-- The List Relator
------------------------------------------------------------------------------

-- ListR, the List "Relator", lifts a binary relation on elements
-- to a binary relation on lists of elements.

data ListR {X Y : Set}(R : X -> Y -> Set) : List X -> List Y -> Set where
  []   : ListR R [] []
  _,-_ : forall {x xs y ys} ->
         R x y -> ListR R xs ys -> ListR R (x ,- xs) (y ,- ys)

-- As you can see, two lists are related by (ListR R) if
--   (i)  their lengths are equal
--   (ii) the elements in corresponding positions are related by R.

-- We will shortly make use of ListR, so you need to build some equipment.


-- ??? 3.16
-- Show that every list is pairwise equal to itself.

listRrefl : forall {X}(xs : List X) -> ListR _==_ xs xs
listRrefl xs = {!!}


-- ??? 3.17
-- Build "map" for ListR.

listR : forall {A B}               -- source element types
               {C D}               -- target element types
        (f : A -> C)(g : B -> D)   -- functions source to target
        {R : A -> B -> Set}        -- relation on source types
        {S : C -> D -> Set}        -- relation on target types
     -> (forall {a b} -> R a b -> S (f a) (g b))  -- source implies target
     -- Now, show why the target lists are related if the source lists are.
     -> forall {as bs} -> ListR R as bs -> ListR S (list f as) (list g bs)
listR f g h rs = {!!}

END OF COMMENT olive-}


{-tamarind UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
-- Cutting Things Up And Sticking Them Back Together
------------------------------------------------------------------------------

-- This section is the heart of the exercise. It deals with the situation
-- where you have a structure that is subdivided in one way, but you need it
-- to be subdivided in another.

-- That's a situation which arises when you need to display multiple layers
-- of overlapping windows. The cutting structure of the front layer
-- determines which parts of the back layers you can see. So you will need
-- to *impose* the front structure onto the back layer, in order to extract
-- its visible parts.

module _ {I}(C : I <| I) where  -- we fix some notion of cutting

-- Agda forces us to develop the general technology before building specific
-- examples. We suggest that you skip forward to the specific example of
-- NatCut, in order to build intuition for what is going on.

-- A "Cutter" is a way of taking a *whole* thing and *choosing* how to cut
-- it into the specified collection of *pieces*.

  Cutter : (I -> Set) -> Set
  Cutter P = {i : I}(c : Cuts C i)   -- given a size, choose how to cut
          -> P i                     -- and, given a whole P,
          -> All P (pieces C c)      -- get all the P pieces for your cut

-- Really, before you go any further, show that you have a NatCut cutter
-- for vectors: see below.

-- Now, working in Tree NatCut, consider that we might have a structure
-- which has a top level cut in one place:
--
--        <---tl---||--------tr-------->
--
-- But suppose we *wish* that it was cut differently, e.g., here:
--
--        <--------wl--------||---wr--->
--
-- If we are able to cut up the recursive substructures wherever we want,
-- we can make our wish come true.
--
-- Project the cut we want onto the cut we've got. And cut there!
--
--        <--------wl--------||---wr--->
--                           ||
--                           vv
--        <---tl---||--------tr-------->
--        <---tl---|<--trl---||--trr-->>
--
-- That is, we leave the left piece alone and cut the right piece in two.
-- In general, some pieces will be left alone; others will be cut.
--
-- We now have three pieces from which we can assemble the structure we
-- need. How to do that?
--
-- Project the cut we've got onto the cut we want. And cut there!
--
--        <---tl---||--------tr-------->
--                 ||
--                 vv
--        <--------wl--------||---wr--->
--        <<--wll--||---wlr-->|---wr--->
--
-- In general, some pieces we want will be whole. Others will need to
-- be assembled from multiple sub-pieces.
--
-- We now have the sizes we need. To finish the job, we just need the
-- means to rearrange the pieces we've got into the structure we want.
--
--        <---tl---|<--trl---||--trr-->>
--        <<--wll--||---wlr-->|---wr--->

-- The following type captures the idea of being kept whole or cut further.

  SubCut : List I    -- a list of sub-piece sizes
        -> I         -- the size of the whole piece
        -> Set
  SubCut is i
    = (is == (i ,- []))  -- kept whole: there is one sub-piece,
                         -- with the same size as the piece
    + (Sg (Cuts C i) \ d -> is == pieces C d)  -- cut further
    -- ^^ there was a cut,  ^^ and the sub-pieces are that cut's pieces

-- Now your turn. We hope this helps you get the idea.

-- ??? 3.18
-- Assemble pieces from sub-pieces.

  glueSubCut : forall {P}
    -> {iss : List (List I)}       -- 2-layer list of sub-pieces you have
    -> {is : List I}               -- 1-layer list of pieces you want
    -> (ds : ListR SubCut iss is)  -- how sub-pieces relate to pieces
    -> All (All (Tree C P)) iss    -- now, given trees as sub-pieces,
    -> All (Tree C P) is           -- make the pieces!
  glueSubCut ds tss = {!!}


-- So, what's the general recipe. Here goes.

  Recutter : Set
  Recutter
    -- You get this information:
    =  {i : I}                         -- the size of the whole
    -> (c : Cuts C i)                  -- the cut we want
    -> (c' : Cuts C i)                 -- the cut we've been given
    -- You produce this information:
    -> Sg (List (List I)) \ iss        -- 2-layer list of wanted sub-pieces
    -> Sg (List (List I)) \ iss'       -- 2-layer list of given sub-pieces
    -> ListR SubCut iss (pieces C c)   -- wanted sub-pieces fit wanted cut
    *  ListR SubCut iss' (pieces C c') -- given sub-pieces fit given cut
    *  (forall {P}           -- whatever the pieces are (i.e., naturally)
        -> All (All P) iss'  -- take the given sub-pieces and
        -> All (All P) iss   -- deliver the wanted sub-pieces
       )


  -- Now, let's work with stuff in Q for which we have a cutter,
  -- and suppose we possess a Recutter.

  module _ {Q}(cutQ : Cutter Q)(recut : Recutter) where

-- ??? 3.19
-- Build a Cutter for trees and a gadget to cut pieces into sub-pieces.

    treeCutter : Cutter (Tree C Q)
    chopSubCut :
         {iss' : List (List I)}          -- sub-piece sizes
      -> {is' : List I}                  -- piece sizes
      -> (ds' : ListR SubCut iss' is')   -- how sub-pieces come from pieces
      -> All (Tree C Q) is'              -- now, given the pieces
      -> All (All (Tree C Q)) iss'       -- produce the sub-pieces

    treeCutter c t = {!!}

    chopSubCut ds' tss = {!!}

-- Hints:
-- (i)   Mutual recursion will probably be necessary.
-- (ii)  Each tree is either a leaf or a node made by some cut you don't want,
--       but you have the equipment to deal with either situation.
-- (iii) "chopSubCut" is a lot like "glueSubCut", only backwards.
-- (iv)  "treeCutter" will need "chopSubCut" and "glueSubCut"

-- And, with that, we're ready to build the key device for working with
-- overlays.

-- ??? 3.20
-- Show that if you can combine a front *piece* with a back *tree*, then
-- you can combine a front *tree* with a back *tree*.

    overlay : forall
         {P}  -- the type of pieces in the front layer
      --  Q, from module parameter above gives the type of pieces at the back
         {R}  -- the type of pieces in the combined output
      -> [        P -:> Tree C Q -:> Tree C R ]  -- front piece on back tree
      -> [ Tree C P -:> Tree C Q -:> Tree C R ]  -- front tree on back tree
    overlay f = {!!}

-- Hints:
-- (i)   Write a recursive program if you like, but do consider whether
--       you can use a recursion scheme instead. Ignoring this hint is its
--       own punishment.
-- (ii)  The "applicative" structure of All may prove useful, as there is
--       an aspect of "zipping" to this problem.


------------------------------------------------------------------------------
-- Cutters for Vectors and Matrices
------------------------------------------------------------------------------

-- ??? 3.21
-- Construct a NatCut cutter for vectors.

vecCutter : forall {X} -> Cutter NatCut (Vec X)
vecCutter c xs = {!!}

-- Hint: see library.

-- Now, a cutter for matrices is a special case of the general idea that
-- if we know how to cut in each dimension separately, we ought to be able
-- to cut multidimensional things, provided we have enough structure to
-- apply "inner" cuts through "outer" layers.
--
-- E.g., as a matrix is a column of rows, cutting vertically is cutting the
-- column, but cutting horizontally is cutting *all* the rows in the column.


-- ??? 3.22
-- Combine two dimensions of cutting.

compCut :
  -- What's the general setup?
  forall {I J}  -- we have an I dimension and a J dimension
  -> (C : I <| I)(F : Set -> I -> Set)
     -- "inner" dimension with C-cuts corresponds to layers of F
  -> (D : J <| J)(G : Set -> J -> Set)
     -- "outer" dimension with D-cuts corresponds to layers of G
  -- What do we know about G?
  -> (forall {X Y j} -> (X -> Y) -> G X j -> G Y j)
     -- it has a suitable "map" operator
  -> (forall {P : I -> Set}{is}{j}
      ->  G (All P is) j -> All (\ i -> G (P i) j) is)
     -- you can "yank" All through it (i.e., it's "traversable")
  -- Now what's the deal? You get
  -> (forall {X} -> Cutter C (F X))  -- a polymorphic C-cutter for Fs
  -> (forall {X} -> Cutter D (G X))  -- a polymorphic D-cutter for Gs
  -- and you make a
  -> forall {X} -- polymorphic
       -> Cutter (C |+| D) -- two-dimensional cutter
           \ { (i , j) -> G (F X i) j}  -- for Gs full of Fs.
compCut C F D G mapG yankG cf dg cut gfx = {!!}


-- ??? 3.23
-- Show that you can "yank" through vectors, and thus acquire your
-- matrix cutter.

vecYank : {P : Nat -> Set} {is : List Nat} {j : Nat} ->
          Vec (All P is) j -> All (\ i -> Vec (P i) j) is
vecYank pss = {!!}

matrixCutter : forall {X} -> Cutter RectCut (Matrix X)
matrixCutter = compCut NatCut Vec NatCut Vec vec vecYank vecCutter vecCutter


------------------------------------------------------------------------------
-- A Recutter for NatCut
------------------------------------------------------------------------------

-- This is a classic exercise in "view" design.

-- Sadly, Agda forces us to present it backwards.

-- Ultimately, your mission will be to implement the following:

natRecutter : Recutter NatCut

-- To do so, you will need to analyse the situation where you have the
-- *same* number, n, cut up in two *different* ways, namely
-- as (x +N x') and as (y +N y').

-- There are three possibilities:

-- x might be less than y (making x' greater than y')
--    <--------------------n------------------>
--    <-----x-----><------------x'------------>
--    <----------y--------><---------y'------->

-- x might be equal to y (making x' equal to y')
--    <--------------------n------------------>
--    <-----------x-----><---------x'--------->
--    <-----------y-----><---------y'--------->

-- x might be greater than y (making x' greater than y')
--    <--------------------n------------------>
--    <----------x--------><---------x'------->
--    <-----y-----><------------y'------------>

-- You will need to design a type

data CutCompare (x x' y y' n : Nat) : Set

-- whose constructors represent the choice between one of these three
-- cases, packing up, in each case, the evidence that is "helpful" about them.

-- You will need to show that, whenever you have two cuts of the same
-- number, you can always get your hands on which case you're in and the
-- "helpful" information about that case.

cutCompare : forall x x' y y' {n}
  -> (x +N x') == n
  -> (y +N y') == n
  -> CutCompare x x' y y' n

-- But what does "helpful" mean? You will find that out when you try to
-- write natRecutter! That will tell you what evidence you *need*.

-- ??? 3.25
-- Give useful arguments to each of the constructors of the following type.

data CutCompare x x' y y' n where
  cutLt : {- what evidence goes here, when x < y ?-}
    CutCompare x x' y y' n
  cutEq : {- what evidence goes here, when x = y ? -}
    CutCompare x x' y y' n
  cutGt : {- what evidence goes here, when x > y ? -}
    CutCompare x x' y y' n

-- ??? 3.26
-- Show that you can get your hands on the evidence.

cutCompare x x' y y' qxx' qyy' = {!!}

-- ??? 3.24
-- Use cutCompare to power natRecutter.

natRecutter (l , r , q) (l' , r' , q') with cutCompare l r l' r' q q'
natRecutter (l , r , q) (l' , r' , q') | cc = {!!}

-- Hint: work backwards, starting with the given, uninformative definition
-- of CutCompare. Try to write natRecutter, and see what evidence is
-- demanded of you in each case. Next, refine the definition of CutCompare
-- to give you the demanded evidence, making sure that you can complete
-- natRecutter as a result. Finally, implement cutCompare to make sure that
-- you can supply the evidence that is demanded.


------------------------------------------------------------------------------
-- Recutters in Multiple Dimensions
------------------------------------------------------------------------------

-- Now that you can recut lengths, it's time to show that you can recut
-- rectangles.

-- In fact, if you can recut individual dimensions, you can recut
-- in any choice of dimensions.

module _                                -- You get:
    {I J}(C : I <| I)(D : J <| J)       -- notions of cut for two dimensions
    (rC : Recutter C)(rD : Recutter D)  -- recutters in both dimensions
  where

-- ??? 3.27
-- Construct a recutter for the pair of dimensions, where each cut can
-- be in either dimension.

  recutPair : Recutter (C |+| D)
  recutPair {i , j} c d = {!!}

-- Hints:
-- (i)   You will find you have four cases, two for each of the following
--       situations:
--       Either the cut wanted and the cut given are in the same dimension
--         (and you have a recutter for that dimension),
--       or the cut wanted and the cut given are in different dimensions,
--         (splitting the space into a kind of "matrix").
-- (ii)  We found it useful to implement the following "plumbing" operators:
{-
plumb : forall {I J K}{P : K -> Set}{f : I -> J -> K}{js : I -> List J} ->
  [ (list (\ i -> list (f i) (js i)) - All (All P)) -:>
    All (\ i -> All (f i - P) (js i)) ]

bmulp : forall {I J K}{P : K -> Set}{f : I -> J -> K}{js : I -> List J} ->
  [ All (\ i -> All (f i - P) (js i)) -:>
    (list (\ i -> list (f i) (js i)) - All (All P)) ]
-}
--       As you can see, they just move index-remapping into and out of the
--       element type in two-layer All-structures.
--       They go just *before* the module declaration.

-- By return of post, you obtain a recutter for RectCut!

rectRecutter : Recutter RectCut
rectRecutter = recutPair NatCut NatCut natRecutter natRecutter

END OF COMMENT tamarind-}


{-aubergine UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
-- Holes and Overlays
------------------------------------------------------------------------------

-- If S is some sort of "stuff", indexed by some sort of size,
-- then Holey S is the sized-indexed choice of "some stuff" or "a hole",
-- i.e., the absence of stuff. The point of a hole is to be *transparent*
-- in a display made of multiple layers.

data Holey {I : Set}(S : I -> Set)(i : I) : Set where
  hole  : Holey S i
  stuff : S i -> Holey S i

-- ??? 3.28
-- Show that if you can cut up "stuff", you can also cut up "holey stuff".

cutHoley : forall {I}(C : I <| I)(S : I -> Set) ->
  Cutter C S -> Cutter C (Holey S)
cutHoley C S cS c hs = {!!}


-- Now, we fix that we are working with rectangular stuff.

module OVERLAYING (S : Nat * Nat -> Set)(cS : Cutter RectCut S) where

  Background Overlay : Nat * Nat -> Set
  Background = Tree RectCut S          -- Backgrounds are made of stuff.
  Overlay    = Tree RectCut (Holey S)  -- Overlays can also have holes.

-- ??? 3.29
-- Show that you can cut overlays.

  overlayCutter : Cutter RectCut Overlay
  overlayCutter = {!!}

-- Hint: Specialise an operation you have already developed.

-- ??? 3.30
-- Show that you can superimpose a "front" overlay on a "back" overlay,
-- or completely fill in all the holes in an overlay, given a background.
-- In each case, the front overlay comes first, the back thing comes second,
-- and the output is the combined thing.

  superimpose : [ Overlay -:> Overlay -:> Overlay ]
  superimpose = {!!}

  backstop : [ Overlay -:> Background -:> Background ]
  backstop = {!!}

-- Hint: This problem was the entire reason for writing "overlay".


------------------------------------------------------------------------------
-- Test Rig for Overlaying
------------------------------------------------------------------------------

-- You will need a correct implementation of both "RectCut" and "treeMatrix"
-- for this test to make sense.

-- With those in place, you should be able to judge your implementation of
-- "superimpose".

module OVERLAYEXAMPLE where

  data Solid {I} : I -> Set where
    solid : Colour -> (i : I) -> Solid i

  cutSolid : Cutter RectCut Solid
  cutSolid c (solid x i) = pureAll (solid x) _

  seeHoleySolid : [ Holey Solid -:> Matrix Char ]
  seeHoleySolid (w , h) hole = vPure (vPure '.')
  seeHoleySolid (w , h) (stuff (solid x ._)) = vPure (vPure (art x)) where
    art : Colour -> Char
    art black   = '#'
    art red     = 'r'
    art green   = 'g'
    art yellow  = 'y'
    art blue    = 'b'
    art magenta = 'm'
    art cyan    = 'c'
    art white   = ' '

  open OVERLAYING Solid cutSolid

  frontExample backExample : Overlay (30 , 20)
  frontExample =
    < inr (5 , 15 , refl)
    ,  leaf hole
    ,- < inr (10 , 5 , refl)
       ,  < inl (5 , 25 , refl)
          ,  leaf hole
          ,- < inl (15 , 10 , refl)
             ,  leaf (stuff (solid red (15 , 10)))
             ,- leaf hole
             ,- [] >
          ,- [] >
       ,- leaf hole
       ,- [] >
    ,- [] >

  backExample =
    < inr (7 , 13 , refl)
    ,  leaf hole
    ,- < inr (10 , 3 , refl)
       ,  < inl (10 , 20 , refl)
          ,  leaf hole
          ,- < inl (15 , 5 , refl)
             ,  leaf (stuff (solid blue (15 , 10)))
             ,- leaf hole
             ,- [] >
          ,- [] >
       ,- leaf hole
       ,- [] >
    ,- [] >

  overlayExample : Overlay (30 , 20)
  overlayExample = superimpose _ frontExample backExample

  see : forall {wh} -> Overlay wh -> List String
  see = treeMatrix seeHoleySolid _ - showMatrix

module _ where
  open OVERLAYEXAMPLE

  seeFront seeBack seeOverlay : List String
  seeFront   = see frontExample
  seeBack    = see backExample
  seeOverlay = see overlayExample

  expectedSeeOverlay : List String
  expectedSeeOverlay =
    ".............................." ,-
    ".............................." ,-
    ".............................." ,-
    ".............................." ,-
    ".............................." ,-
    ".....rrrrrrrrrrrrrrr.........." ,-
    ".....rrrrrrrrrrrrrrr.........." ,-
    ".....rrrrrrrrrrrrrrrbbbbb....." ,-
    ".....rrrrrrrrrrrrrrrbbbbb....." ,-
    ".....rrrrrrrrrrrrrrrbbbbb....." ,-
    ".....rrrrrrrrrrrrrrrbbbbb....." ,-
    ".....rrrrrrrrrrrrrrrbbbbb....." ,-
    ".....rrrrrrrrrrrrrrrbbbbb....." ,-
    ".....rrrrrrrrrrrrrrrbbbbb....." ,-
    ".....rrrrrrrrrrrrrrrbbbbb....." ,-
    "..........bbbbbbbbbbbbbbb....." ,-
    "..........bbbbbbbbbbbbbbb....." ,-
    ".............................." ,-
    ".............................." ,-
    ".............................." ,- []

  checkSeeOverlay : seeOverlay == expectedSeeOverlay
  checkSeeOverlay = {!!}  -- this should be provable with refl

END OF COMMENT aubergine-}


{-banana UNCOMMENT WHEN YOU REACH THIS PART OF THE EXERCISE

------------------------------------------------------------------------------
-- Overlays for Applications
------------------------------------------------------------------------------

open OVERLAYING (Matrix ColourChar) matrixCutter

-- For the rest of the exercise, we instantiate the "stuff" in an Overlay
-- to be matrices of coloured characters. That's exactly what we can display
-- in the terminal window.


------------------------------------------------------------------------------
-- Application Layers
------------------------------------------------------------------------------

-- An AppLayer refines the notion of display used in an application.
-- Instead of being a matrix of coloured characters, it is an Overlay,
-- which means it can have *holes*. Later, we'll look at how to superimpose
-- multiple layers.

AppLayer : Nat * Nat -> Set
AppLayer = Server AppInterface (Overlay :*: CursorPosition)

-- ??? 3.31
-- Reconstruct the simple "rectApp" application as an AppLayer, generalising
-- it to allow the colour to be chosen.

rectAppLayer : Colour -> Char -> [ AppLayer ]
rectAppLayer x c wh = {!!}

-- ??? 3.32
-- Show how to turn an AppLayer into an Application.

runAppLayer : [ AppLayer -:> Application ]

-- Specification:
-- (i)   Any holes in the AppLayer should be filled with white spaces.
-- (ii)  The "stuff" in the AppLayer should display as it is given.
-- (iii) The Application should react as given by the AppLayer.

runAppLayer wh layer = {!!}

-- Hints:
-- (iv)  Note that the type ensures that the Overlay is the size of the
--       screen.
-- (v)   You have already done the hard work by writing "treeMatrix" and
--       "backstop".


------------------------------------------------------------------------------
-- Applications in a Window
------------------------------------------------------------------------------

-- ??? 3.33
-- Write a function which takes an application of any size and displays it
-- as a window at a given position in a screen of any size.

windowLayer : forall (x y : Nat)   -- left and top coordinates of window
              appWH                -- width and height of window application
           -> AppLayer appWH       -- the application to put in the window
           -> [ AppLayer ]         -- an application which fills the screen

-- Specification:
-- (i)   Any part of the screen not occupied by the application should
--       display as a hole.
-- (ii)  If the application does not fit entirely on the screen, you should
--       display the largest top-left corner of it that does fit.
-- (iii) Trap the arrow keys to move the window without resizing it.
-- (iv)  Trap the shifted arrow keys to resize the window without moving
--       its top left corner.

windowLayer x y (aw , ah) layer (sw , sh) = {!!}

-- Hints:
-- (v)   You will need to compare positions and sizes in a way that generates
--       the evidence you need to inform cropping and padding. Consider
--       constructing a "view" which captures "less-or-equal" concretely:
--       Given two numbers, n and m,
--         either m is (n +N d) for some d (so n is less than or equal to m),
--         or n is (m +N suc d) for some d (so n is greater than m).
--       It may help to repackage the CutCompare "view".
-- (vi)  Padding amounts to filling parts of the screen with holes.
-- (vii) You should find overlayCutter useful.


------------------------------------------------------------------------------
-- Layering Applications
------------------------------------------------------------------------------

-- ??? 3.34
-- Write a function which combines two layers into one.

twoLayers : [ AppLayer -:> AppLayer -:> AppLayer ]
--            ^^ front     ^^ back      ^^ combined

-- Specification:
-- (i)   The combined display should show the front display, except where it
--       has holes. You should make sure we can see through the holes in the
--       front to the display at the back, showing what's in those places.
-- (ii)  Trap the tab key, making it swap the front and back layers.
-- (iii) All other keystrokes should be handled by the front layer.

twoLayers wh front back = {!!}

-- Hints:
-- (iv)  superimpose
-- (v)   How should "resize" events be handled? What do the types make you do?

END OF COMMENT banana-}


------------------------------------------------------------------------------
-- The Main Program
------------------------------------------------------------------------------

-- We've given you a succession different versions of the main program to try
-- with the compiler. The first should be ready to run from the beginning.
-- The rest become gradually available as you complete more of the exercise.
-- Of course, you can only try one at a time, keeping the others commented
-- out.

main : IO One
-- The following should work now.
main = appMain (rectApp '*')
{- -- when you have rectAppLayer working, try this
main = appMain \ wh -> runAppLayer wh (rectAppLayer green '*' _)
-}
{- -- when you also have windowLayer working, try this
main = appMain \ wh -> runAppLayer wh
  (windowLayer 2 2 (30 , 20) (rectAppLayer green '*' _) _)
-}
{- -- when you have everything working, try this
main = appMain \ wh -> runAppLayer wh
  (twoLayers wh
    (windowLayer 2 2 (30 , 20) (rectAppLayer green '*' _) wh)
    (windowLayer 12 4 (30 , 20) (rectAppLayer blue '.' _) wh))
-}

{-
To compile, move to your CS410 directory and invoke
  agda --compile --ghc-flag "-lncurses" Exercise/Three.agda

To run the program,
  ./Three

Ctrl-C quits the running application.
-}

