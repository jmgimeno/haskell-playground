{-# LANGUAGE DataKinds                      #-}
{-# LANGUAGE EmptyCase                      #-}
{-# LANGUAGE GADTs                          #-}
{-# LANGUAGE InstanceSigs                   #-}
{-# LANGUAGE KindSignatures                 #-}
{-# LANGUAGE LambdaCase                     #-}
{-# LANGUAGE MultiParamTypeClasses          #-}
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

module Singletons.Part3 where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude hiding (And, Or)
import           Data.Singletons.TH
import           Data.Void

$(singletons [d|
  data DoorState = Opened | Closed | Locked
    deriving (Show, Eq)
  |])

data Door :: DoorState -> Type where
    UnsafeMkDoor :: { doorMaterial :: String } -> Door s

mkDoor :: Sing s -> String -> Door s
mkDoor _ = UnsafeMkDoor

data SomeDoor :: Type where
    MkSomeDoor :: Sing s -> Door s -> SomeDoor

mkSomeDoor :: DoorState -> String -> SomeDoor
mkSomeDoor ds mat = withSomeSing ds $ \dsSing ->
    MkSomeDoor dsSing (mkDoor dsSing mat)

data Knockable :: DoorState -> Type where
    KnockClosed :: Knockable 'Closed
    KnockLocked :: Knockable 'Locked

knock :: Knockable s -> Door s -> IO ()
knock _ d = putStrLn $ "Knock knock on " ++ doorMaterial d ++ " door!"

class Proved p a where
    auto :: p a

instance Proved Knockable 'Closed where
    auto = KnockClosed

instance Proved Knockable 'Locked where
    auto = KnockLocked

isKnockable :: Sing s -> Decision (Knockable s)
isKnockable = \case
    SOpened -> Disproved $ \case {}    -- s ~ 'Opened
    SClosed -> Proved KnockClosed      -- s ~ 'Closed
    SLocked -> Proved KnockLocked      -- s ~ 'Locked

disproveOpened :: Knockable 'Opened -> Void
disproveOpened k = case k of {}             -- empty pattern match

knockSomeDoor
    :: SomeDoor     -- ^ status not known until you pattern match at runtime
    -> IO ()
knockSomeDoor (MkSomeDoor s d) = case isKnockable s of
    Proved k    -> knock k d
    Disproved _ -> putStrLn "No knocking allowed!"

$(singletons [d|
  data Pass = Obstruct | Allow
    deriving (Show, Eq)

  statePass :: DoorState -> Pass
  statePass Opened = Allow
  statePass Closed = Obstruct
  statePass Locked = Obstruct
  |])

knockP :: (StatePass s ~ 'Obstruct) => Door s -> IO ()
knockP d = putStrLn $ "Knock knock on " ++ doorMaterial d ++ " door!"

knockSomeDoorP
    :: SomeDoor     -- ^ status not known until you pattern match at runtime
    -> IO ()
knockSomeDoorP (MkSomeDoor s d) = case sStatePass s of
    SObstruct -> knockP d                        -- `StatePass s ~ 'Obstruct`
    SAllow    -> putStrLn "No knocking allowed!" -- `StatePass s ~ 'Allow`

main :: IO ()
main = return ()

-- Exercises

{-

1. We talk about predicates as type constructors with type k -> Type. This fits 
a lot of things we’ve seen before (all instances of Functor, for example), 
but some predicates are more interesting than others.

What is the interpretation of SDoorState as a predicate? (remember, SDoorState 
s is the type synonym for Sing (s :: DoorState)) What “traditional” (that is, 
a -> Bool) predicate does it correspond to?

What is the type of its decision function? Can you implement it?

=> The predicate `SDoorState` (and really, the predicate for `Sing` for any
specific kind instance) is essentially `const True`, the always True predicate

-}

decideDoorState :: Sing s -> Decision (SDoorState s)
decideDoorState = Proved

