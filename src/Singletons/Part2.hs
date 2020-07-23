{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE UndecidableInstances #-}

module Singletons.Part2 where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.TH

$(singletons [d|
  data DoorState = Opened | Closed | Locked
    deriving (Show, Eq)
  |])

data Door :: DoorState -> Type where
    UnsafeMkDoor :: { doorMaterial :: String } -> Door s

closeDoor :: Door 'Opened -> Door 'Closed
closeDoor (UnsafeMkDoor m) = UnsafeMkDoor m

lockDoor :: Door 'Closed -> Door 'Locked
lockDoor (UnsafeMkDoor m) = UnsafeMkDoor m

openDoor :: Door 'Closed -> Door 'Opened
openDoor (UnsafeMkDoor m) = UnsafeMkDoor m

doorStatus :: Sing s -> Door s -> DoorState
doorStatus SOpened _ = Opened
doorStatus SClosed _ = Closed
doorStatus SLocked _ = Locked

lockAnyDoor :: Sing s -> (Door s -> Door 'Locked)
lockAnyDoor = \case
    SOpened -> lockDoor . closeDoor
    SClosed -> lockDoor
    SLocked -> id

doorStatus_ :: SingI s => Door s -> DoorState
doorStatus_ = doorStatus sing

lockAnyDoor_ :: SingI s => Door s -> Door 'Locked
lockAnyDoor_ = lockAnyDoor sing

mkDoor :: Sing s -> String -> Door s
mkDoor _ = UnsafeMkDoor

data SomeDoor :: Type where
    MkSomeDoor :: Sing s -> Door s -> SomeDoor

fromDoor :: Sing s -> Door s -> SomeDoor
fromDoor = MkSomeDoor

fromDoor_ :: SingI s => Door s -> SomeDoor
fromDoor_ = fromDoor sing

closeSomeOpenedDoor :: SomeDoor -> Maybe SomeDoor
closeSomeOpenedDoor (MkSomeDoor s d) = case s of
    SOpened -> Just . fromDoor_ $ closeDoor d
    SClosed -> Nothing
    SLocked -> Nothing

lockAnySomeDoor :: SomeDoor -> SomeDoor
lockAnySomeDoor (MkSomeDoor s d) = fromDoor_ $ lockAnyDoor s d

mkSomeDoor :: DoorState -> String -> SomeDoor
mkSomeDoor ds = case toSing ds of
    SomeSing s -> fromDoor s . mkDoor s

withDoor :: DoorState -> String -> (forall s. Sing s -> Door s -> r) -> r
withDoor ds m f = withSomeSing ds $ \s -> f s (mkDoor s m)

main :: IO ()
main = return ()

-- Exercise 1
-- Let’s revisit our original redundant SomeDoor, compared to our final SomeDoor.

data OldSomeDoor :: Type where
    OldMkSomeDoor :: DoorState -> String -> OldSomeDoor

-- To help convince yourself that the two are equal, write functions converting between the two:

-- Avoid directly pattern matching on the singletons or constructors. 
-- Instead, use singletons library tools like toSing, withSomeSing, fromSing,  etc.

toOld :: SomeDoor -> OldSomeDoor
toOld (MkSomeDoor s d) = 
    OldMkSomeDoor (fromSing s) (doorMaterial d)

fromOld :: OldSomeDoor -> SomeDoor
fromOld (OldMkSomeDoor ds m) = 
    mkSomeDoor ds m

-- Exercise 2
{-
Previously, we had an unlockDoor function that took an Int (the “password”) with a 
Door 'Locked and returned a Maybe (Door 'Closed). It returns a Door 'Closed (unlocked door) 
in Just if an odd number was given, and Nothing otherwise (a failed unlock)

Use this to implement a that would return a SomeDoor. Re-use the “password” logic from the 
original unlockDoor. If the door is successfully unlocked (with a Just), return the unlocked 
door in a SomeDoor. Otherwise, return the original locked door (in a SomeDoor).
-}

unlockDoor :: Int -> Door 'Locked -> Maybe (Door 'Closed)
unlockDoor n (UnsafeMkDoor m)
    | n `mod` 2 == 1 = Just (UnsafeMkDoor m)
    | otherwise      = Nothing

unlockSomeDoor :: Int -> Door 'Locked -> SomeDoor
unlockSomeDoor n d = 
    case unlockDoor n d of
        Nothing -> fromDoor_ d
        Just d' -> fromDoor_ d'

-- Exercise 3

-- Implement openAnyDoor' in the same style, with respect to openAnyDoor:

openAnyDoor :: SingI s => Int -> Door s -> Maybe (Door 'Opened)
openAnyDoor n = openAnyDoor_ sing
  where
    openAnyDoor_ :: Sing s -> Door s -> Maybe (Door 'Opened)
    openAnyDoor_ = \case
      SOpened -> Just
      SClosed -> Just . openDoor
      SLocked -> fmap openDoor . unlockDoor n

openAnySomeDoor :: Int -> SomeDoor -> SomeDoor
openAnySomeDoor n sd@(MkSomeDoor s d) = withSingI s $
    case openAnyDoor n d of
        Nothing -> sd
        Just d' -> fromDoor_ d'

-- Exercise 4

-- Write the SingKind instance for the promoted kind of a custom list type:

data List a = Nil | Cons a (List a)

data SList :: List a -> Type where
    SNil  :: SList 'Nil
    SCons :: Sing x -> SList xs -> SList ('Cons x xs)

type instance Sing = SList

instance SingKind k => SingKind (List k) where
    type Demote (List k) = List (Demote k)

    fromSing :: Sing (xs :: List k) -> List (Demote k)
    fromSing = \case
        SNil -> Nil
        SCons sx sxs -> Cons (fromSing sx) (fromSing sxs)

    toSing :: List (Demote k) -> SomeSing (List k)
    toSing = \case
        Nil -> SomeSing SNil
        Cons x xs -> withSomeSing x $ \sx ->
                     withSomeSing xs $ \sxs ->
            SomeSing (SCons sx sxs)

