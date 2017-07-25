{-
    Fun with Profunctors
    Phil Freeman

    https://www.youtube.com/watch?v=OJtGECfksds
-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module FunWithProfunctors where

import Control.Arrow ((***), (&&&))
import Data.Tuple (swap)

-- Functor

--class Functor f where
--    fmap :: (a -> b) -> f a -> f b

data Burrito filling = Tortilla filling

instance Functor Burrito where
    fmap f (Tortilla filling)
        = Tortilla (f filling)

-- Contravariant Functors

class Contravariant f where
    cmap :: (a -> b) -> f b -> f a

data Customer filling = Eat (filling -> IO ())

instance Contravariant Customer where
    cmap f (Eat eat) = Eat (eat . f)

-- Aside

{-
    * Something is a Functor when its type argument only
    appears in positive position
    * Something is a Contravariant when its type argument only
    appears in negative position

    +a
    -a -> +a
    -a -> -a -> +a
    (+a -> -a) -> +a
    ((-a -> +a) -> -a) -> +a
-}

-- Invariant Functors

class Invariant f where
    imap :: (b -> a) -> (a -> b) -> f a -> f b

data Endo a = Endo (a -> a)

instance Invariant Endo where
    imap f g (Endo e) = Endo (g . e . f)

    -- What can we do with Invariant functors?
    -- Not much but:

data Iso' a b = Iso' (a -> b) (b -> a)

iso :: Invariant f => Iso' a b -> f a -> f b
iso (Iso' to from) = imap from to

    -- Invariant functor can be quite tricky to work with
    -- The Functor => Applicative => Monad hierarchy doesn't 
    -- seem to fit
    -- To map we have to be able to invert the function we
    -- want to map

    -- Instead split the type argumento into two

-- Profunctors

class Profunctor p where
    dimap :: (a -> b) -> (c -> d) -> p b c -> p a d

instance Profunctor (->) where
    dimap f g k = g . k . f

    -- We get the same lifting operation from before

isoP :: Profunctor p => Iso' a b -> p a a -> p b b
isoP (Iso' to from) = dimap from to

swapping :: Profunctor p => p (a, b) (x, y)
                         -> p (b, a) (y, x)
swapping = dimap swap swap

assoc :: Profunctor p => p ((a, b), c) ((x, y), z)
                      -> p (a, (b, c)) (x, (y, z))
assoc = dimap (\(a, (b, c))-> ((a, b), c)) 
              (\((a, b), c) -> (a, (b, c)))

{-
*FunWithProfunctors> :t swapping . swapping 
swapping . swapping
  :: Profunctor p => p (b, a) (y, x) -> p (b, a) (y, x)
*FunWithProfunctors> : t assoc . swapping

*FunWithProfunctors> :t assoc . swapping
assoc . swapping
  :: Profunctor p =>
     p (c, (a, b)) (z, (x, y)) -> p (a, (b, c)) (x, (y, z))
-}

-- Examples

data Forget r a b = Forget { runForget :: a -> r }

instance Profunctor (Forget r) where
    dimap f _ (Forget forget) = Forget (forget . f)

data Star f a b = Star { runStar :: a -> f b }

instance Functor f => Profunctor (Star f) where
    dimap f g (Star star) = Star (fmap g . star . f)

data Costar f a b = Costar { runCostar :: f a -> b }

instance Functor f => Profunctor (Costar f) where
    dimap f g (Costar costar) = Costar (g . costar . fmap f)

data Fold m a b = Fold { runFold :: (b -> m) -> a -> m }

instance Profunctor (Fold m) where
    dimap f g (Fold fold) = Fold $ \k -> fold (k . g) . f

data Mealy a b = Mealy { runMealy :: a -> (b, Mealy a b) }

instance Profunctor Mealy where
    dimap f g = go
        where 
            go (Mealy mealy) = Mealy $ (g *** go) . mealy . f

-- Strengthening Profunctors

class Profunctor p => Strong p where
    first  :: p a b -> p (a, x) (b, x)
    second :: p a b -> p (x, a) (x, b)

instance Strong (->) where
    first  f (a, x) = (f a, x)
    second f (x, a) = (x, f a)

    -- Examples:

instance Strong (Forget r) where
    first  (Forget ar) = Forget $ ar . fst
    second (Forget ar) = Forget $ ar . snd 

instance Functor f => Strong (Star f) where
    first  (Star afb) = Star $ \(a, x) -> fmap (,x) (afb a) 
    second (Star afb) = Star $ \(x, a) -> fmap (x,) (afb a)

class Functor w => Comonad w where
    extract   :: w a -> a
    duplicate :: w a -> w (w a)
    extend    :: (w a -> b) -> w a -> w b

instance Comonad w => Strong (Costar w) where
    {-
    (w a -> b) -> w (a, x) -> (b, x) 
    first  (Costar wab) = Costar $ \wax -> let b = wab (fmap fst wax)
                                               x = snd (extract wax)
                                           in (b, x)
    -}
    first  (Costar wab) = Costar $ wab . fmap fst &&& snd . extract
    second (Costar wab) = Costar $ fst . extract  &&& wab . fmap snd

instance Strong (Fold m) where
    first  (Fold fold) = Fold $ \bx_m (a, x) -> fold (\b -> bx_m (b, x)) a
    second (Fold fold) = Fold $ \xb_m (x, a) -> fold (\b -> xb_m (x, b)) a

instance Strong Mealy where
    {-
    first  (Mealy mealy) = Mealy $ \(a, x) -> let (b, mab) = mealy a
                                              in ((b, x), dimap fst (,x) mab)
    -}
    first  (Mealy mealy) = Mealy $ \(a, x) -> ((,x) *** dimap fst (,x)) (mealy a)
    second (Mealy mealy) = Mealy $ \(x, a) -> ((x,) *** dimap snd (x,)) (mealy a)

{-
    * Try composing these:

    first          :: Strong p => p a b -> p (a, x) (b, x)
    first . first  :: Strong p => p a b -> p ((a, x), x1) ((b, x), x1)
    first . second :: Strong p => p a b -> p ((x, a), x1) ((x, b), x1)

    * Our new functions alsp compose with isos:

    assoc . first :: Strong p => p (a, b) (x, y) 
                              -> p (a, (b, z)) (x, (y, z))
  
    These are starting to look a lot like lenses!
-}

-- Profunctor Lenses

type Iso  s t a b = forall p. Profunctor p => p a b -> p s t
type Lens s t a b = forall p. Strong p     => p a b -> p s t

    -- Note: every iso is automatically a lens!

-- Lenses as Isos

    -- Consider how we can construct a lens
    -- type Lens s t a b = forall p. Strong p => p a b -> p s t

    -- All we have are dimap and first
    -- dimap :: Profuctor f => (c -> a) -> (b -> d) -> p a b -> p c d
    -- first :: Strong p => p a b -> p (a, x) (b, x)

    -- Every profunctor lens has a normal form

nf :: (s -> (a, x)) -> ((b, x) -> t) -> Lens s t a b
nf f g pab = dimap f g (first pab)

    -- Comment on video: Every van Leuhoven (traditional) lens 
    -- Lens s t a b = forall Functor f => (a -> f b) -> s -> f t
    -- can be encoded int the profuctor version using Star as p
    -- He's not sure about the other way around.

    -- The idea is to find an s which is isomorphic to (a, x)
    -- The "changing types" iso is given by f and g so, given
    -- p a b,  we can convert s to a and the rest, and changing 
    -- a to b, we can reintegrate (b, x) into t, so having p s t

    -- In other words:

iso2lens :: Iso s t (a, x) (b, x) -> Lens s t a b
iso2lens iso pab = iso (first pab)

    -- A lens asserts that the family of types given by s and t
    -- is (uniformly) isomorphic to a product

    -- We can con the other way with some work

-- lens2iso :: Lens s t a b -> exists x. Iso s t (a, x) (b, x)

-- Lens Combinators

    -- Let's write some useful functions with lenses:

get :: Lens s t a b -> s -> a
get lens = runForget (lens (Forget id))

set :: Lens s t a b -> b -> s -> t
set lens b = lens (const b)

modify :: Lens s t a b -> (a -> b) -> s -> t
modify lens f = lens f

    -- We didn't really need a full lens
    
-- Choice

class Profunctor p => Choice p where
    left  :: p a b -> p (Either a x) (Either b x)
    right :: p a b -> p (Either x a) (Either x b)

    -- The function arrow has choice

instance Choice (->) where
    left  f (Left a)  = Left (f a)
    left  _ (Right x) = Right x
    right _ (Left x)  = Left x
    right f (Right a) = Right (f a)

    -- Choice will identify big structures with Either
    -- So parts can exist or not and this corresponds to
    -- prisms.

    -- Examples

instance Monoid m => Choice (Forget m) where
    left  (Forget am) = Forget $ either am (const mempty)
    right (Forget am) = Forget $ either (const mempty) am
 
instance Applicative f => Choice (Star f) where
    left  (Star f) = Star $ either (fmap Left . f) (pure . Right)
    right (Star f) = Star $ either (pure . Left) (fmap Right . f) 

instance Comonad w => Choice (Costar w) where
    left  (Costar f) 
        = Costar $ \weax -> case extract weax of
                                Left  a -> Left $ f $ fmap (const a) weax
                                Right x -> Right x 
    right (Costar f) 
        = Costar $ \wexa -> case extract wexa of
                                Right a -> Right $ f $ fmap (const a) wexa
                                Left  x -> Left x 

instance Monoid m => Choice (Fold m) where
    {-
    left  (Fold fold) = Fold $ \ebx_m eax -> case eax of
                                                Left a -> fold (ebx_m . Left) a
                                                Right x -> ebx_m (Right x)
    -}
    left  (Fold fold) 
        = Fold $ \ebx_m -> either (fold (ebx_m . Left)) (ebx_m . Right)
    right (Fold fold) 
        = Fold $ \ebx_m -> either (ebx_m . Left) (fold (ebx_m . Right)) 

instance Choice Mealy where
    left  = undefined
    right = undefined

    -- Remember that in the van Leuhoven presentation we get
    -- prisms by using Applicative. Here is the same because
    -- get use Star as the choice (which need Applicative)

    -- left and right compose as before

    {-
        left         :: Choice p => p a b 
                                 -> p (Either a x) (Either b x)
 
        left . left  :: Choice p => p a b 
                                 -> p (Either (Either a x) x1) 
                                      (Either (Either b x) x1)

        left . right :: Choice p => p a b 
                                 -> p (Either (Either x a) x1) 
                                      (Either (Either x b) x1)
    -}

    -- left and right compose with isos and lenses

    {-
        first . left :: (Choice p, Strong p) => p a b 
                                             -> p (Either a x, x1) 
                                                  (Either b x, x1)

        left . first :: (Strong p, Choice p) => p a b 
                                             -> p (Either (a, x) x1) 
                                                  (Either (b, x) x1)
    -}

-- Prisms

    -- We've rediscovered Prisms !!

    -- type Iso  s t a b = forall p. Profunctor p => p a b -> p s t
    -- type Lens s t a b = forall p. Strong p     => p a b -> p s t

type Prism s t a b = forall p. Choice p => p a b -> p s t

    -- Note: every Iso is automatically a Prism!

-- 0-1 Traversals

type AffineTraversal s t a b = forall p. (Strong p, Choice p) => p a b -> p s t

-- first . left :: AffineTraversal (Either a x, y) (Either b x, y) a b

    -- It's an optic in which you can have 0-1 occurrences of
    -- the thing
    -- The difference with a lens is that you cannot reconstruct the
    -- bigger thing

-- Prisms as Isos

    -- Normal forms for prisms

iso2prism :: Iso s t (Either a x) (Either b x) -> Prism s t a b
iso2prism iso pab = iso (left pab)

    -- A prism asserts that the family of types given by s and t
    -- is (uniformly) isomorphic to a sum

-- Arrows

{-
class (Strong a, Category a) => Arrow a

instance Arrow (->)
instance Applicative f => Arrow (Star f)
instance Comonad w => Arrow (Costar w)
instance Monoid m => Arrow (Fold m)
instance Arrow Mealy

-}

-- Proc Notation

{-

{# LANGUAGE Arrows #}

assoc :: Arrow a => a b c -> a (b, x) (c, x)
assoc arr = proc (b, x) -> do
                c <-( arr <-( b
                returnA <-( (c, x)

-}

-- More Optics

type Optic c s t a b = forall p. c p => p a b -> p s t

-- type Iso       = Optic Profunctor
-- type Lens      = Optic Strong
-- type Prim      = Optic Choice
type Traversal s t a b = Optic Traversing s t a b
type Grate     s t a b = Optic Closed s t a b
-- type SEC       = Optic ((->) ~) -- Structural Editing Combinator

class (Strong p, Choice p) => Traversing p where
    traversing :: Traversable t => p a b -> p (t a) (t b)

class Profunctor p => Closed p where
    closed :: p a b -> p (x -> a) (x -> b)

    -- We get some contraint on p and we get an optic
{-
    Iso              Profunctor     s_i ~ a_i
    Lens             Strong         s_i ~ (a_i, x)
    Prism            Choice         s_i ~ Either a_i x
    Traversal        Traversing     s_i ~ t a_i
    Grate            Closed         s_i ~ x -> a_i
    AffineTraversal  Strong,Choice  s_i ~ Either (a_i, x) y
-}

    -- For isntanmce Iso sayss is isomorphic to a

-- Pros & Cons

    -- Pros
        -- More consistent API
        -- Many optics can be "inverted"
        -- We can apply our optics to more structures

    -- Cons
        -- Indexed optic story isn't great
        -- Some changes to the API needed for performance

-- Real-World Example

{-
-- data UI state = UI { runUI :: (state -> IO ()) -> state -> IO Widget }

    -- This is an invariant functor because state appears in both
    -- positive and negative positions

data UI b a = UI { runUI :: (a -> IO ()) -> b -> IO Widget }

    -- So we split the state type into two

instance Profunctor UI
instance Strong UI
instance Choice UI
instance Traversing UI

type UI' state = UI state state

animate :. UI' state -> state -> IO ()
animate ui state = do
    widget <- runUI ui (animate ui) state
    render widget

    -- The more instances we can create, the more lifting capabilities
    -- we have

first      :: UI' state -> UI' (state, x)
left       :: UI' state -> UI' (Either state x)
traversing :: UI' state -> UI' [state]

https://github.com/zrho/purescript-optic-ui

-}

