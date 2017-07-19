{-
    Bartosz Milevski - Arrows are Strong Arrows are Profunctors
    https://www.youtube.com/watch?v=hrNfkP8iKAs
-}

{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}

module ArrowsAreStrongProfunctors where

import Control.Monad ((>=>))
import qualified GHC.Base (id, (.))
import Prelude (Int, ($), Monad, return)

-- CATEGORY

class Category cat where
    id  :: a `cat` a 
    (.) :: cat b c -> cat a b -> cat a c

instance Category (->) where
    id  = GHC.Base.id
    (.) = (GHC.Base..)

-- MONOID

class Monoid m where
    mu  :: (m, m) -> m
    eta :: () -> m

newtype IntFun = IF (Int -> Int)

instance Monoid IntFun where
    mu (IF f, IF g) = IF (g . f)
    eta () = IF id

-- PROFUNCTOR

class Functor (f :: * -> *) where
    fmap :: (a -> b) -> f a -> f b

class BiFunctor (f :: * -> * -> *) where
    bimap :: (a -> a') -> (b -> b') -> f a b -> f a' b'

class ProFunctor (p :: * -> * -> *) where
    dimap :: (a' -> a) -> (b -> b') -> p a b -> p a' b'

instance ProFunctor (->) where
    dimap con pro f = pro . f . con

-- END

type End p = forall x. p x x

newtype NatPro f g a b = NatPro (f a -> g b)

instance (Functor f, Functor g) => ProFunctor (NatPro f g) where
    dimap ba cd (NatPro g) = NatPro $ fmap cd . g . fmap ba

type Nat f g = End (NatPro f g)

    -- type Nat f g = forall x. f x -> g x 

-- COEND

    -- type Coend p = exists x. p x x

data Coend p = forall x. Coend (p x x)

    -- (exists x. C x) -> y  ~  forall x. C x -> y

-- COMPOSITION

    -- Profuctor as proof relevant relation between types
    -- So you compose profucntors the same way you compose relations

    -- type Compose p q a b = exists x. (p a x, q x b)

data Compose p q a b = forall x. Compose (p a x) (q x b)

instance (ProFunctor p, ProFunctor q) =>
    ProFunctor (Compose p q) where
        dimap con pro (Compose pax qxb) =
            Compose (dimap con id pax) (dimap id pro qxb)

-- COMPOSITION AS COEND

data TenProd p q a b x y = TenProd (p a y) (q x b)

instance (ProFunctor p, ProFunctor q) =>
    ProFunctor (TenProd p q a b) where
        dimap con pro (TenProd pay qxb) =
            TenProd (dimap id pro pay) (dimap con id qxb)

type Compose' p q a b = Coend (TenProd p q a b)

-- THE YONEDA LEMMA

    -- The Ninja Yoneda Lemmma

newtype PreYoneda f a x y = PreYoneda ((a -> x) -> f y)

instance Functor f => ProFunctor (PreYoneda f a) where
    dimap con pro (PreYoneda ax_fy) =
        PreYoneda (\ax' -> fmap pro (ax_fy (con . ax')))

    -- End (PreYoneda f a) = forall x. PreYoneda f a x x

type Yoneda' f a = End (PreYoneda f a)

newtype Yoneda f a = Yoneda (forall x. (a -> x) -> f x)

    -- Yoneda f a ~ f a

toY :: Functor f => Yoneda f a -> f a
toY (Yoneda axfx) = axfx id

fromY :: Functor f => f a -> Yoneda f a
fromY fa = Yoneda (\ax -> fmap ax fa)

-- COYONEDA

    -- CoYoneda f a ~ f a
    -- type CoYoneda f a = exists x. (x -> a, f x)

data CoYoneda f a = forall x. CoYoneda (x -> a) (f x)

toCY :: Functor f => CoYoneda f a -> f a
toCY (CoYoneda xa fa) = fmap xa fa

fromCY :: Functor f => f a -> CoYoneda f a
fromCY fa = CoYoneda id fa

-- RIGHT UNIT OF COMPOSITION

{-
    type Compose p q a b = exists x. (p a x, q x b)

    Compose p (->) a b ~
    exists x. (p a x, x -> b) ~
    exists x. (x -> b, p a x) ~
    CoYoneda (p a) b ~
    p a b

-}

-- LEFT UNIT OF COMPOSITION 

{-
    type Compose p q a b = exists x. (p a x, q x b)

    forall c. (Compose (->) p a b -> c) ~
    forall c. (exists x. (a -> x, p x b) -> c) ~
    forall c x. (a -> x, p x b) -> c ~
    forall c x. (a -> x) -> p x b -> c ~
    forall c x. (a -> x) -> (p x b -> c) ~
    forall c. Yoneda (p _ b -> c) a ~
    forall c. p a b -> c

    So Compose (->) p a b ~ p a b
-}

-- PROFUCTOR CATEGORY

    -- Objects: types
    -- Morphisms: profunctors (composition, identity)

    -- Objects: profuctors (C^op x C -> Set)
    -- Morphisms: natural transformations

    -- Monoidal Category
        -- Objects: profunctors
        -- Morphisms: natural transformations
        -- Product: Profunctor composition
        -- Unit: Hom-profumctor (->)

-- PRE-ARROWS

    -- Monoid in the category od profunctors
        -- object p
        -- mu  :: p * p -> p
        -- eta :: i -> p
    
    {-
        mu :: Compose p p a b -> p a b
    
            (exists x. p a x, p x b) -> p a b ~ 
            forall x. (p a x, p x b) -> p a b ~
            forall x. p a x -> p x b -> p a b 

            (>>>) :: p a x -> p x b -> p a b

        eta :: (->) a b -> p a b

        arr :: (a -> b) -> p a b
    -}

-- PROFUNCTOR STRENGTH

class ProFunctor p => Strong p where
    first :: p a b -> p (a, x) (b, x)

    -- Unit and multiplication preserve strength

-- ARROWS

    -- Arrow is a monoid in the category of strong profunctors

class Category ar => Arrow ar where
    arr :: (a -> b) -> ar a b
    first' :: ar a b -> ar (a, c) (b, c)

infix 1 >>>
(>>>) :: (Arrow ar) => ar a b -> ar b c -> ar a c
a >>> a' = a' . a

-- KLEISLI ARROW

data Kleisli m a b = Kl (a -> m b)

instance Monad m => Arrow (Kleisli m) where
    arr f = Kl (return . f)
    first' (Kl f) = Kl (\(x, c) -> do y <- f x
                                      return (y, c))

instance Monad m => Category (Kleisli m) where
    id = arr id
    (Kl f) . (Kl g) = Kl (g >=> f)

-- CONCLUSIONS

    -- Juggling categories
    -- Morphisms in one category are objects in another category

    -- Combining structures
    -- Monoidal category = category + monoid
