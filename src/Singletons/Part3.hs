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

{-

2. Now let’s practice working with predicates, singletons, and negation via 
Refuted together.

You may have heard of the principle of “double negation”, where not (not p) 
implies p. So, we should be able to say that Refuted (Refuted (Knockable s)) 
implies Knockable s. If something is not “not knockable”, then it must 
be knockable, right?

Try writing refuteRefuteKnockable to verify this principle — at least for 
the Knockable predicate.

While not required, I recommend using isKnockable and writing your 
implementation in terms of it! Use sing to give isKnockable the singleton 
it needs.

Hint: You might find absurd (from Data.Void) helpful:

absurd :: forall a. Void -> a

If you have a Void, you can make a value of any type!

-}

refuteRefuteKnockable
    :: forall s. SingI s
    => Refuted (Refuted (Knockable s))
    -> Knockable s
refuteRefuteKnockable rrK = 
    case isKnockable sing of
        Proved k -> k
        Disproved rK -> absurd $ rrK rK

{-

    
3. (This next one is fairly difficult compared to the others, and is only 
tangentially related to singletons, so feel free to skip it!)

Type-level predicates are logical constructs, so we should be able to define 
concepts like “and” and “or” with them.

 a. Define a predicate constructor And that takes two predicates and returns a 
    new predicate. This new predicate is true (aka, has an inhabitant) if and 
    only if the two original predicates are true (aka, have inhabitants)
-}

data And :: (k -> Type) -> (k -> Type) -> (k -> Type) where
    And :: l s -> r s -> (And l r) s

{-

 b. Define a predicate constructor Or that takes two predicates and returns 
    a new predicate. This new predicate is true (aka, has an inhabitant) if 
    and only if at least one of the two original predicates are true (aka, 
    have inhabitants)

    There are potentially multiple non-trivial variations of this type.

    Do And and Or look similar to any types you might have encountered in 
    the past? Maybe, perhaps, similiar to types that are a part of basic 
    beginner Haskell concepts?

    => (a, b) and Either a b
-}

data Or :: (k -> Type) -> (k -> Type) -> (k -> Type) where
    OrL :: l s -> (Or l r) s
    OrR :: r s -> (Or l r) s

{-

 c. Maybe surprisingly, And p q and Or p q are decidable if p and q are. 
    Can we write the decision functions?

    These functions actually demonstrate, I feel, why Decision having both 
    a Proved a and Disproved (Refuted a) branch is very useful. This is 
    because, if you wrote the structure of And and Or correctly, it’s 
    impossible to incorrectly define decideAnd and decideOr. You can’t 
    accidentally say false when it’s true, or true when it’s false — your 
    implementation is guarunteed correct.
-}

decideAnd
    :: (forall x. Sing x -> Decision (p x))
    -> (forall x. Sing x -> Decision (q x))
    -> Sing a
    -> Decision (And p q a)
decideAnd dp dq sa 
    = decideAnd' (dp sa) (dq sa)
        where
            decideAnd' :: Decision (p a) -> Decision (q a) -> Decision (And p q a)
            decideAnd' (Proved pa) (Proved qa) = Proved $ And pa qa
            decideAnd' (Disproved rPa) _ = Disproved $ \(And pa _) -> rPa pa
            decideAnd' _ (Disproved rQa) = Disproved $ \(And _ qa) -> rQa qa


decideOr
    :: (forall x. Sing x -> Decision (p x))
    -> (forall x. Sing x -> Decision (q x))
    -> Sing a
    -> Decision (Or p q a)
decideOr dp dq sa 
    = decideOr' (dp sa) (dq sa)
        where
            decideOr' :: Decision (p a) -> Decision (q a) -> Decision (Or p q a)
            decideOr' (Proved pa) _ = Proved $ OrL pa
            decideOr' _ (Proved qa) = Proved $ OrR qa
            decideOr' (Disproved rPa) (Disproved rQa) 
                = Disproved $ \case 
                    OrL pa -> rPa pa
                    OrR qa -> rQa qa

{-

 d. Now let’s use And and Or to prove some useful facts about Knockable and 
    ('Opened :~:). We know that it’s impossible for something to be both 
    Knockable and ('Opened :~:) (that is, both knockable and equal to 'Opened). 
    Write such a witness:
-}

knockableNotOpened
    :: forall s. SingI s
    => Refuted (And Knockable ((:~:) 'Opened) s)
knockableNotOpened (And k o) = case k of
    KnockClosed -> case o of {} -- no constructor of type ('Opened :~: 'Closed)
    KnockLocked -> case o of {} -- no constructor of type ('Opened :~: 'Locked)

{-
    We also know that a given DoorState is either Knockable or ('Opened :~:) — 
    at least one of these is always true. Write such a witness:  
-}

knockableOrOpened
    :: forall s. SingI s
    => Or Knockable ((:~:) 'Opened) s
knockableOrOpened = case sing @s of
    SOpened -> OrR $ Refl
    SClosed -> OrL KnockClosed
    SLocked -> OrL KnockLocked

{-
 4. Instead of creating an entire Knocked type, we could have just said 
 “as long as the door is not 'Opened, you can knock”. This means we could 
 write knock as:

 knock :: Refuted (s :~: 'Opened) -> Door s -> IO ()

 Which we must pass a proof that s is not equal to 'Opened in order to 
 open our door.

 Is this really the same thing? Is Refuted (s :~: 'Opened) the same thing 
 as Knockable s?

 Let’s try to say that the two things are the same! Write the following 
 functions to show that Refuted (s :~: 'Opened) is the same logical predicate 
 as Knockable s!

 Note: knockedRefute is fairly straightforward, but refuteKnocked is definitely 
 trickier, so don’t be discouraged!

 Hint: See the note about absurd from Exercise 2!
-}

knockedRefute
    :: forall s. SingI s
    => Knockable s
    -> Refuted (s :~: 'Opened)
knockedRefute k 
    = case k of
        KnockClosed -> \case {}  -- no ctors of type 'Closed :~: 'Opened
        KnockLocked -> \case {}  -- no ctors of type 'Locked :~: 'Opened

refuteKnocked
    :: forall s. SingI s
    => Refuted (s :~: 'Opened)
    -> Knockable s
refuteKnocked rE = case sing @s of
    SOpened -> absurd $ rE Refl
    SClosed -> KnockClosed
    SLocked -> KnockLocked

{-

5. On our type level function version of knock, we wrote, with a constraint:

knock :: (StatePass s ~ 'Obstruct) => Door s -> IO ()
knock d = putStrLn $ "Knock knock on " ++ doorMaterial d ++ " door!"

We can muddy the waters a bit, for fun, by having this take a proof of the 
constraint instead:

knockRefl :: (StatePass s :~: 'Obstruct) -> Door s -> IO ()
knockRefl _ d = putStrLn $ "Knock knock on " ++ doorMaterial d ++ " door!"

Rewrite a version of knockSomeDoor in terms of knockRefl, called knockSomeDoorRefl:

Remember not to use knock!

Assume that DoorState has an instance of SDecide, so you can use (%~). This should be 
derived automatically as long as you derive Eq:

$(singletons [d|
  data DoorState = Opened | Closed | Locked
    deriving (Show, Eq)
  |])

-}

knockRefl :: (StatePass s :~: 'Obstruct) -> Door s -> IO ()
knockRefl _ d = putStrLn $ "Knock knock on " ++ doorMaterial d ++ " door!"

knockSomeDoorRefl
    :: SomeDoor
    -> IO ()
knockSomeDoorRefl (MkSomeDoor s d) = case sStatePass s of
    SAllow -> putStrLn "cannot know on opened door !"
    SObstruct -> knockRefl Refl d

-- Official solution:

knockSomeDoorRefl'
    :: SomeDoor
    -> IO ()
knockSomeDoorRefl' (MkSomeDoor s d) =
    case sStatePass s %~ SObstruct of
      Proved r    -> knockRefl r d
      Disproved _ -> putStrLn "No knocking allowed!"