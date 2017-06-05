{-# LANGUAGE TupleSections #-}

import Tree
import Data.List (maximumBy, minimumBy, sortBy)
import Data.Map.Strict (fromListWith, assocs)
import Data.Maybe (mapMaybe)
import Data.Ord (comparing)
import System.Environment (getArgs)

size :: Tree -> Integer
size (Plus a b)    = 1 + size a + size b
size (Minus a b)   = 1 + size a + size b
size (Times a b)   = 1 + size a + size b
size (Divide a b)  = 1 + size a + size b
size (Expt a b)    = 1 + size a + size b
size (Negate a)    = 1 + size a
size (Sqrt a)      = 1 + size a
size (Factorial a) = 1 + size a + 1 -- prefer solutions w/o !
size (Four)        = 1

evaluated :: [(Int, Tree)]
evaluated = mapMaybe (\t -> (,t) <$> evalToInt t) $ trees $ replicate 4 Four

solutions :: ((Tree -> Tree -> Ordering) -> [Tree] -> Tree) -> [(Int, Tree)]
solutions p = sortBy (comparing fst) $ singleSolutions where
  singleSolutions = assocs $ fromListWith preferred evaluated
  preferred a b   = p (comparing size) [a, b]

ordering :: [String] -> (Tree -> Tree -> Ordering) -> [Tree] -> Tree
ordering ["-c"] = maximumBy
ordering ["-s"] = minimumBy
ordering _      = minimumBy

main :: IO ()
main = do
  args <- getArgs
  mapM_ print (solutions $ ordering args)
