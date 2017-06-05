{-
  Why Functional Programming Matters
  John Hughes, Mary Sheeran (Lambda Days 2017)
-}

{-# LANGUAGE RankNTypes #-}

module Church where

-- Booleans

true  x y = x
false x y = y

ifte bool t e = bool t e

-- Positive integers

zero f x = x
one  f x = f x
two  f x = f (f x)

add m n f x = m f (n f x)
mul m n f x = m (n f) x

exp m n = n m


-- Factorial

fact :: (forall a. (a -> a) -> a -> a) -> (a -> a) -> a -> a
fact n =
  ifte (iszero n)
       one
       (mul n (fact (decr n)))

iszero n =
  n (\_ -> false) true

decr n =
  n (\m f x -> f (m incr zero))
    zero
    (\x -> x)
    zero

incr n f x =
  f (n f x)

-- Predecessor in wikipedia

decr' n f x =
  n (\g h -> h (g f)) (\_ -> x) (\u -> u)

minus m n = (n decr) m
