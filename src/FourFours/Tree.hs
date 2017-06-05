module Tree (
  Tree(Plus,
       Minus,
       Times,
       Divide,
       Expt,
       Negate,
       Sqrt,
       Factorial,
       Four),
  eval,
  evalToInt,
  trees ) where

import Control.Monad (liftM, liftM2, mfilter)
import Data.List (inits, tails)

data Tree = Plus Tree Tree
          | Minus Tree Tree
          | Times Tree Tree
          | Divide Tree Tree
          | Expt Tree Tree
          | Negate Tree
          | Sqrt Tree
          | Factorial Tree
          | Four
  deriving (Read, Show)

trees :: [Tree] -> [Tree]
trees [x] = [ f x | f <- [ id, Negate, Sqrt, Factorial ] ]
trees xs = do
  (left, right) <- splits xs
  t1            <- trees left
  t2            <- trees right
  p             <- pairs t1 t2
  trees [p]

splits :: [a] -> [([a], [a])]
splits xs = init $ tail $ zip (inits xs) (tails xs)

pairs :: Tree -> Tree -> [Tree]
pairs a b = [ f a b | f <- [ Plus, Minus, Times, Divide, Expt ] ]

eval :: Tree -> Maybe Float
eval (Plus a b)  = binop (+) a b
eval (Minus a b) = binop (-) a b
eval (Times a b) = binop (*) a b
eval (Expt a b)  = binop (**) a b
eval (Divide a b) = liftM2 (/) (eval a) (mfilter (/=0) (eval b))
eval (Negate a) = unaryop (0-) a
eval (Sqrt a)   = unaryop sqrt a
eval (Factorial Four) = Just (4 * 3 * 2)
eval (Factorial _)    = Nothing
eval Four = Just 4

binop :: (Float -> Float -> Float) -> Tree -> Tree -> Maybe Float
binop op a b = liftM2 op (eval a) (eval b)

unaryop :: (Float -> Float) -> Tree -> Maybe Float
unaryop op a = liftM op (eval a)

evalToInt :: Tree -> Maybe Int
evalToInt t = round <$> mfilter good (eval t)

good :: Float -> Bool
good v = 0 <= v && v <= 20 && isInt v

isInt :: Float -> Bool
isInt n = fromIntegral (round n :: Int) == n
