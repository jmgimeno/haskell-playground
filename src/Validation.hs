module Validation where

import Control.Applicative

data Validation a = Error [String] | Value a
  deriving Show

instance Functor Validation where
  fmap f (Value a) = Value (f a)
  fmap f (Error e) = Error e

instance Applicative Validation where
  pure = Value
  (Value f) <*> (Value x)  = Value (f x)
  (Error s) <*> (Error s') = Error (s ++ s')
  (Error s) <*> _          = Error s
  _         <*> (Error s)  = Error s

pos :: Int -> Validation Int
pos x = if (x > 0)
        then Value x
        else Error [show x ++ " should be > 0"]

neg :: Int -> Validation Int
neg x = if (x < 0)
        then Value x
        else Error [show x ++ " should be < 0"]

{-
*Main> (+) <$> (pos 1) <*> (pos 3)
Value 4
*Main> (+) <$> (pos 1) <*> (neg 3)
Error ["3 must be > 0"]
*Main> (+) <$> (neg 1) <*> (pos (-1))
Error ["1 must be > 0","-1 must be > 0"]
*Main>
-}

-- We need to explicit the type due to the
-- Monomorphism Restriction
plus :: (Num a, Applicative f) => f a -> f a -> f a
plus = liftA2 (+)

{-
*Main> plus (pos 1) (pos 3)
Value 4
*Main> plus (pos 1) (neg 3)
Error ["3 must be > 0"]
*Main> plus (neg 1) (pos (-1))
Error ["1 must be > 0","-1 must be > 0"]
*Main>
-}
