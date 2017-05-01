Lenses: compositional data access and manipulation.
  Simon Peyton Jones
  Edward Kmett
  09/10/2013

  https://skillsmatter.com/skillscasts/4251-lenses-compositional-data-access-and-manipulation

The Basic Idea
==============

* A lens provides access into the middle of a data structure, or container
* Access = read, write, modify, (later) fold, traverse, etc
* A lens is a first-class value, with a type Lens' s a
  s: type of the container
  a: type of the focus
* Eg Lens' DateTime Mins
     Lens' DateTime Hours
* Lenses compose:
  composeL :: Lens' s1 s2
           -> Lens' s2 a
           -> Lens' s1 a

Why do we want that?
====================

data Person = P { name :: String
                 , addr :: Address
                 , salary :: Int }

data Address = A { road :: String
                  , city :: String
                  , postcode :: String }
-- addr :: Person -> Address

setName :: String -> Person -> Person
setName n p = p { name = n }

setPostcode :: String -> Person -> Person
setPostcode pc p = p { addr = addr p { postcode = pc } }

* This sort of code gets tiresome very fast

What we want
============

> data Person = P { name :: String
>                 , addr :: Address
>                 , salary :: Int }

> data Address = A { road :: String
>                  , city :: String
>                  , postcode :: String }

* A lens for each field

> lname   :: Lens' Person String
> laddr   :: Lens' Person Address
> lsalary :: Lens' Person Int

> lroad     :: Lens' Address String
> lcity     :: Lens' Address String
> lpostcode :: Lens' Address String

* A way to use the lens to get and update

> view :: Lens' s a -> s -> a
> set  :: Lens' s a -> a -> s -> s

* A way to compose lenses

> composeL :: Lens' s1 s2 -> Lens' s2 a -> Lens' s1 a

If we had that...
=================

> setPostcode :: String -> Person -> Person
> setPostcode pc p = set (laddr `composeL`lpostcode) pc p

* (it is a composite lens)
* More useful way to compose !!!

The obvious first attempt
=========================

* A lens is just a record with a getter and a setter

> data LensR s a = L { viewR :: s -> a
>                    , setR  :: a -> s -> s }

> composeL (L v1 u1) (L v2 u2)
>   = L (\s -> v2 (v1 s))
>       (\a s -> u1 (u2 a (v1 s)) s)

* This works, but...
* Inefficient. Suppose you want to modify a field, this

> over :: LensR s a -> (a -> a) -> s -> s
> over ln f s = setR ln (f (viewR ln s)) s

  Doing view then update is Not Cool

* You could add a mofify method... but...

Inflexible
==========

* What about a modification that might fail?

modifyM :: LensR s a -> (a -> Maybe a) -> s -> Maybe s

* Or that are effect-ful?

modifyIO :: LensR s a -> (a -> IO a) -> s -> IO s

* Each one seems to require a new function... that we can add to the record

data LensR s a
  = L { viewR :: s -> a
      , setR  :: a -> s -> s
      , mod   :: (a -> a) -> s -> s
      , modM  :: (a -> Maybe a) -> s -> Maybe s
      , modIO :: (a -> IO a) -> s -> IO s }

Inflexible?
===========

* But those modifications are similar
* Maybe we can unify them

data LensR s a
  = L { viewR :: s -> a
      , setR  :: a -> s -> s
      , mod   :: (a -> a) -> s -> s
      , modF  :: Functor f => (a -> f a) -> s -> f s }

...and that is a REALLY good idea !!!

* Remember Functor

class Functor f where
  fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
  fmap _ Nothing = Nothing
  fmap f (Just x) = Just (f x)

instance Functor [] where
  fmap _ [] = []
  fmap f (x:xs) = f x : fmap f xs

* The magic moment happens when someone realizes that we can do all of them with only modF !!!

One function to rule them all
=============================

* Twan van Laarhoven
* Edward Kmett

> type Lens' s a = forall f . Functor f
>                         => (a -> f a) -> s -> f s

* WTF ?

data LensR s a = L { viewR :: s -> a
                   , setR  :: a -> s -> s }

* It's going to turn out that
  - Lens' and LensR are isomorphic

> lensToLensR :: Lens' s a -> LensR s a
> lensRToLens :: LensR s a -> Lens' s a

  - But Lens' is better

How are we going to do the set?
===============================

type Lens' s a = forall f . Functor f
                        => (a -> f a) -> s -> f s
data LensR s a = L { viewR :: s -> a
                   , setR  :: a -> s -> s }

set :: Lens' s a -> (a -> s -> s)
set ln a s = ...   ln returns a value of type f s
                   but we want a value of type s

* The way to fet from (f s) to s is to choose the Identity Functor as f

> newtype Identity a = Identity a

> runIdentity :: Identity a -> a
> runIdentity (Identity x) = x

> instance Functor Identity where
>   fmap f (Identity x) = Identity (f x)

> set :: Lens' s a -> (a -> s -> s)
> set ln x s
>   = runIdentity (ln set_fld s)
>     where set_fld :: a -> Identity a
>           set_fld _ = Identity x

That is, we discard current value and return new value x

- ln lifts set_fld :: a -> Identity a to a function s -> Identity s
- runIdentity removes the Identity constructor

* Or, as Edward Kmett would write it:

> const :: a -> b -> a
> const x _ = x

> set :: Lens' s a -> (a -> s -> s)
> set ln x = runIdentity . ln (Identity . const x)

And, in the same spirit
=======================

set :: Lens' s a -> (a -> s -> s)
set ln x = runIdentity . ln (Identity . const x)

> over :: Lens' s a -> (a -> a) -> s -> a
> over ln f = runIdentity . ln (Identity . f)

Which is a lot more efficient than the get/set idea we hold before

Same again... using a lens to view
==================================
