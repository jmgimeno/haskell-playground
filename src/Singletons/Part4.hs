{-# LANGUAGE AllowAmbiguousTypes            #-}
{-# LANGUAGE DataKinds                      #-}
{-# LANGUAGE EmptyCase                      #-}
{-# LANGUAGE GADTs                          #-}
{-# LANGUAGE InstanceSigs                   #-}
{-# LANGUAGE KindSignatures                 #-}
{-# LANGUAGE LambdaCase                     #-}
{-# LANGUAGE MultiParamTypeClasses          #-}
{-# LANGUAGE NoStarIsType                   #-}
{-# LANGUAGE RankNTypes                     #-}
{-# LANGUAGE ScopedTypeVariables            #-}
{-# LANGUAGE StandaloneDeriving             #-}
{-# LANGUAGE TemplateHaskell                #-}
{-# LANGUAGE TypeApplications               #-}
{-# LANGUAGE TypeFamilies                   #-}
{-# LANGUAGE TypeInType                     #-}
{-# LANGUAGE TypeOperators                  #-}
{-# LANGUAGE UndecidableInstances           #-}
{-# OPTIONS_GHC -Wall                       #-}
{-# OPTIONS_GHC -Werror=incomplete-patterns #-}

module Singletons.Part4 where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude hiding    (And, Or, sFoldr, FoldrSym0, FoldrSym1, FoldrSym2, FoldrSym3, Foldr)
import           Data.Singletons.Sigma
import           Data.Singletons.TH hiding         (sFoldr, FoldrSym0, FoldrSym1, FoldrSym2, FoldrSym3, Foldr, sFold, Fold)
import           Data.Singletons.TypeLits

$(singletons [d|
  data DoorState = Opened | Closed | Locked
    deriving (Show, Eq, Ord)
  |])

data Door :: DoorState -> Type where
    UnsafeMkDoor :: { doorMaterial :: String } -> Door s

mkDoor :: Sing s -> String -> Door s
mkDoor _ = UnsafeMkDoor

$(singletons [d|
  mergeState :: DoorState -> DoorState -> DoorState
  mergeState = max
  |])

mergeDoor
    :: Door s
    -> Door t
    -> Door (MergeState s t)
mergeDoor d e = UnsafeMkDoor $ doorMaterial d ++ " and " ++ doorMaterial e

type SomeDoor = Sigma DoorState (TyCon1 Door)

mkSomeDoor :: DoorState -> String -> SomeDoor
mkSomeDoor ds mat = withSomeSing ds $ \dsSing ->
    dsSing :&: mkDoor dsSing mat

mergeSomeDoor :: SomeDoor -> SomeDoor -> SomeDoor
mergeSomeDoor (s :&: d) (t :&: e) =
    sMergeState s t :&: mergeDoor d e

data Hallway :: [DoorState] -> Type where
    HEnd  :: Hallway '[]        -- ^ end of the hallway, a stretch with no
                                --   doors
    (:<#) :: Door s
          -> Hallway ss
          -> Hallway (s ': ss)  -- ^ A door connected to a hallway is a new
                                --   hallway, and we track the door's state
                                --   in the list of hallway door states
infixr 5 :<#

$(singletons [d|
  mergeStateList :: [DoorState] -> DoorState
  mergeStateList []     = Opened               -- the identity of mergeState
  mergeStateList (s:ss) = s `mergeState` mergeStateList ss
  |])

collapseHallway :: Hallway ss -> Door (MergeStateList ss)
collapseHallway HEnd       = mkDoor SOpened "End of Hallway"
collapseHallway (d :<# ds) = d `mergeDoor` collapseHallway ds

type SomeHallway = Sigma [DoorState] (TyCon1 Hallway)

collapseSomeHallway :: SomeHallway -> SomeDoor
collapseSomeHallway (ss :&: d) = sMergeStateList ss
                             :&: collapseHallway d

$(singletons [d|
  foldr :: (a -> b -> b) -> b -> [a] -> b
  foldr _ z []     = z
  foldr f z (x:xs) = f x (foldr f z xs)
  |])

-- | COMMENT THIS OUT IF YOU WANT TO RUN ON SINGLETONS < 2.5 OR GHC 8.4
$(singletons [d|
  fold :: Monoid b => [b] -> b
  fold []     = mempty
  fold (x:xs) = x <> fold xs

  instance Semigroup DoorState where
      (<>) = mergeState
  instance Monoid DoorState where
      mempty  = Opened
      mappend = (<>)
  |])

collapseHallway'
    :: Hallway ss
    -> Door (Fold ss)
collapseHallway' HEnd       = UnsafeMkDoor "End of Hallway"
collapseHallway' (d :<# ds) = d `mergeDoor` collapseHallway' ds

collapseSomeHallway' :: SomeHallway -> SomeDoor
collapseSomeHallway' (ss :&: d) =
        sFold ss
    :&: collapseHallway' d

-- | END OF SINGLETONS-2.5 ONLY SECTON

collapseHallway''
    :: Hallway ss
    -> Door (FoldrSym2 MergeStateSym0 'Opened @@ ss)
collapseHallway'' HEnd       = UnsafeMkDoor "End of Hallway"
collapseHallway'' (d :<# ds) = d `mergeDoor` collapseHallway'' ds

collapseSomeHallway'' :: SomeHallway -> SomeDoor
collapseSomeHallway'' (ss :&: d) =
        sFoldr (singFun2 @MergeStateSym0 sMergeState) SOpened ss
     -- or
     -- sFoldr (sing @MergeStateSym0) SOpened ss
    :&: collapseHallway'' d


-- Exercises

-- | Supplementary definitions
data Knockable :: DoorState -> Type where
    KnockClosed :: Knockable 'Closed
    KnockLocked :: Knockable 'Locked

$(singletons [d|
  data Pass = Obstruct | Allow
    deriving (Show, Eq, Ord)

  statePass :: DoorState -> Pass
  statePass Opened = Allow
  statePass Closed = Obstruct
  statePass Locked = Obstruct
  |])

{-

1. Let’s try combining type families with proofs! In doing so, hopefully 
we can also see the value of using dependent proofs to show how we can 
manipulate proofs as first-class values that the compiler can verify.

Remember Knockable from Part 3?

data Knockable :: DoorState -> Type where
    KnockClosed :: Knockable 'Closed
    KnockLocked :: Knockable 'Locked

Closed and Locked doors are knockable. But, if you merge two knockable
doors…is the result also always knockable?

I say yes, but don’t take my word for it. Prove it using Knockable!

mergedIsKnockable
    :: Knockable s
    -> Knockable t
    -> Knockable (MergeState s t)

mergedIsKnockable is only implementable if the merging of two DoorStates 
that are knockable is also knockable. See if you can write the implementation!
-}

mergedIsKnockable
    :: Knockable s
    -> Knockable t
    -> Knockable (MergeState s t)
mergedIsKnockable s t = case (s, t) of
  (KnockClosed, KnockClosed) -> KnockClosed
  (KnockClosed, KnockLocked) -> KnockLocked
  (KnockLocked, KnockClosed) -> KnockLocked
  (KnockLocked, KnockLocked) -> KnockLocked

{-

2. Write a function to append two hallways together.

appendHallways
    :: Hallway ss
    -> Hallway ts
    -> Hallway ????

from singletons — implement any type families you might need from scratch!

Remember the important principle that your type family must mirror the 
implementation of the functions that use it.

Next, for fun, use appendHallways to implement appendSomeHallways:

type SomeHallway = Sigma [DoorState] (TyCon1 Hallway)

appendSomeHallways
    :: SomeHallway
    -> SomeHallway
    -> SomeHallway
-}
$(singletons [d|
  append :: [a] -> [a] -> [a]
  append []     ys = ys
  append (x:xs) ys = x : append xs ys
  |])

appendHallways
    :: Hallway ss
    -> Hallway ts
    -> Hallway (Append ss ts)
appendHallways = \case
    HEnd     -> id
    d :<# ds -> \es -> d :<# appendHallways ds es

appendSomeHallways
    :: SomeHallway
    -> SomeHallway
    -> SomeHallway
appendSomeHallways (ss :&: ds) (ts :&: es)
      = sAppend ss ts
    :&: appendHallways ds es

{-

3. Can you use Sigma to define a door that must be knockable?

To do this, try directly defining the defunctionalization symbol 
KnockableDoor :: DoorState ~> Type (or use singletons to generate it 
for you — remember that singletons can also promote type families) 
so that:

type SomeKnockableDoor = Sigma DoorState KnockableDoor

will contain a Door that must be knockable.

Try doing it for both (a) the “dependent proof” version (with the 
Knockable data type) and for (b) the type family version (with the 
StatePass type family).

Solutions here! I gave four different ways of doing it, for a full 
range of manual vs. auto-promoted defunctionalization symbols and 
Knockable vs. Pass-based methods.

Hint: Look at the definition of SomeDoor in terms of Sigma:

type SomeDoor = Sigma DoorState (TyCon1 Door)

Hint: Try having KnockableDoor return a tuple.
-}

-- Auto-promotion, Knockable
$(singletons [d|
  type KnockableDoor1 s = (Knockable s, Door s)
  |])

type SomeKnockableDoor1 = Sigma DoorState KnockableDoor1Sym0

-- Manual family, Knockable
data KnockableDoor2 :: DoorState ~> Type
type instance Apply KnockableDoor2 s = (Knockable s, Door s)

type SomeKnockableDoor2 = Sigma DoorState KnockableDoor2

-- Auto-promotion, via Pass
$(singletons [d|
  type KnockableDoor3 s = (StatePass s :~: 'Obstruct, Door s)
  |])

type SomeKnockableDoor3 = Sigma DoorState KnockableDoor3Sym0

-- Manual family, via Pass
data KnockableDoor4 :: DoorState ~> Type
type instance Apply KnockableDoor4 s = (StatePass s :~: 'Obstruct, Door s)

type SomeKnockableDoor4 = Sigma DoorState KnockableDoor4

{-

4. Take a look at the API of the Data.Singletons.TypeLits module, based on 
the API exposed in GHC.TypeNats module from base.

Using this, you can use Sigma to create a predicate that a given Nat number 
is even:

data IsHalfOf :: Nat -> Nat ~> Type
type instance Apply (IsHalfOf n) m = n :~: (m * 2)

type IsEven n = Sigma Nat (IsHalfOf n)

(*) is multiplication from the Data.Singletons.Prelude.Num module. (You must 
have the -XNoStarIsType extension on for this to work in GHC 8.6+), and :~: is 
the predicate of equality from Part 3:

data (:~:) :: k -> k -> Type where
    Refl :: a :~: a

(It’s only possible to make a value of type a :~: b using Refl :: a :~: a, so 
it’s only possible to make a value of that type when a and b are equal. I like 
to use Refl with type application syntax, like Refl @a, so it’s clear what we 
are saying is the same on both sides; Refl @a :: a :~: a)

The only way to construct an IsEven n is to provide a number m where m * 2 is n. 
We can do this by using SNat @m, which is the singleton constructor for the Nat 
kind (just like how STrue and SFalse are the singleton constructors for the Bool 
kind):

tenIsEven :: IsEven 10
tenIsEven = SNat @5 :&: Refl @10
    -- Refl is the constructor of type n :~: (m * 2)
    -- here, we use it as Refl @10 :: 10 :~: 10

-- won't compile
sevenIsEven :: IsEven 10
sevenIsEven = SNat @4 :&: Refl
    -- won't compile, because we need something of type `(4 * 2) :~: 7`,
    -- but Refl must have type `a :~: a`; `8 :~: 7` is not constructable
    -- using `Refl`.  Neither `Refl @8` nor `Refl @7` will work.
Write a similar type IsOdd n that can only be constructed if n is odd.

type IsOdd n = Sigma Nat (???? n)
And construct a proof that 7 is odd:

sevenIsOdd :: IsOdd 7

On a sad note, one exercise I’d like to be able to add is to ask you to 
write decision functions and proofs for IsEven and IsOdd. Unfortunately, 
Nat is not rich enough to support this out of the box without a lot of 
extra tooling!
-}

data IsHalfOf :: Nat -> Nat ~> Type
type instance Apply (IsHalfOf n) m = n :~: (m * 2)

type IsEven n = Sigma Nat (IsHalfOf n)

tenIsEven :: IsEven 10
tenIsEven = SNat @5 :&: Refl

data IsHalfOfMinusOne :: Nat -> Nat ~> Type
type instance Apply (IsHalfOfMinusOne n) m = n - 1 :~: m * 2

type IsOdd n = Sigma Nat (IsHalfOfMinusOne n)

sevenIsOdd :: IsOdd 7
sevenIsOdd = SNat @3 :&: Refl

