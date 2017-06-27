
-- Simple back-tracking search with delimited control
-- Illustrating shift/reset, and the application of different search 
-- strategies to the same program without re-writing it

module Searches where

import Control.Monad.Cont hiding (mplus)
import System.Environment (getArgs)

-- Lazy search tree
-- which is the result of a non-deterministic expression.
-- Thunks are important to _prevent_ memoization so that we 
-- could examine the tree several times without fully expanding it. 
-- Iterative deepening below critically relies on that property.

data SearchTree a = Leaf a | Node [() -> SearchTree a]

-- Different search strategies can be implemented as operations
-- on the search tree.

-- Depth-first search

dfs :: SearchTree a -> [a]
dfs (Leaf x) = [x]
dfs (Node b) = concatMap (\x -> dfs $ x ()) b

-- Breadth-first search

bfs :: SearchTree a -> [a]
bfs tree = loop [\() -> tree]
 where
 loop []    = []
 loop (h:t) = case h () of
               Leaf x -> x : loop t
               Node b -> loop (t ++ b)

-- Iterative deepening
-- It should be obvious that the code repeatedly expands the nodes
-- of the tree as it examines the tree deeper and deeper.
-- One is tempted to eliminate the repetition (e.g., by changing
-- the SearchTree declaration to take advantage of GHC's memoization).
-- However, that will miss the point: re-evaluating the same
-- expressions (nodes) over and over again is the essence of
-- iterative deepening. The algorithm trades time for space:
-- for very large search trees, it is overall better to recompute the 
-- nodes than to store them.
-- The algorithm is complete, like BFS -- it always finds a solution if one
-- exists -- and yet is memory-efficient as DFS.
-- BFS takes so much memory, to store the frontier of the search,
-- that it becomes impractical for even the moderate toy problems.

-- Collect the values from the leaves whose distance from
-- the root is exactly d.
-- Return Nothing if d is greater than the depth of the tree
-- The clause `depth_search d (Node [])' proved very useful:
-- It plugs the memory leak.

depth_search :: Int -> SearchTree a -> Maybe [a]
depth_search 0 (Leaf x) = Just [x]
depth_search d (Leaf _) = Nothing
depth_search d (Node [])= Nothing
depth_search 0 (Node _) = Just []
depth_search d (Node b) = 
  foldr (\t a -> join (depth_search (d-1) (t ())) a)  Nothing b
 where join x Nothing = x
       join Nothing x = x
       join (Just l1) (Just l2) = Just (l1 ++ l2)

iter_deepening :: SearchTree a -> [a]
iter_deepening t = loop 0
 where
 loop d = check d (depth_search d t)
 check d Nothing  = []
 check d (Just l) = l ++ loop (d+1)


-- Other search strategies can be added easily.


-- Reifying a non-deterministic program as a search tree
-- Notably we do _not_ use SearchTree itself as a monad


-- Defining shift/reset in terms of Cont
runC :: Cont w w -> w
runC m = runCont m id

reset :: Cont a a -> Cont w a
reset = return . runC

shift :: ((a -> w) -> Cont w w) -> Cont w a
shift f = Cont (runC . f)

-- Non-deterministic choice from a _finite_ list
-- This is the only primitive. Everything else is implemented in terms
-- of choose
choose :: [a] -> Cont (SearchTree w) a
choose lst = shift (\k -> return $ Node (map (\x () -> k x) lst))

-- Failing computation
failure :: Cont (SearchTree w) a
failure = choose []

-- How to run non-deterministic computation
reify :: Cont (SearchTree a) a -> SearchTree a
reify m = runC (fmap Leaf m)


-- With Cont and reification, we separate the vexing issues of the search
-- strategy from constructing a computation.


-- Examples: computing Pythagorean triples

ex1 = reify $ do
  x <- choose [1..10]
  y <- choose [1..10]
  z <- choose [1..10]
  if x*x + y*y == z*z then return (x,y,z) else failure


test1d = dfs ex1
-- [(3,4,5),(4,3,5),(6,8,10),(8,6,10)]

test1b = bfs ex1
-- the same, but takes 8 times more memory

test1i = iter_deepening ex1
-- about as much memory as DFS


-- Non-deterministic choice from a potentially _infinite_ list

-- First, we define mplus to join two computations together.
-- We define mplus in terms of choose
mplus :: Cont (SearchTree w) a -> Cont (SearchTree w) a -> 
	 Cont (SearchTree w) a
-- mplus e1 e2 = choose [e1,e2] >>= id

-- or we may inline choose and simplify a bit:
mplus e1 e2 = shift (\f -> 
  return $ Node [\ () -> runCont (e1 >>= return . f) id,
		 \ () -> runCont (e2 >>= return . f) id])

-- We may further hand-optimize that expression to the following.
-- But it leaks memory! It retains the constructed tree
-- mplus e1 e2 = Cont (\k -> Node [\() -> runCont e1 k,
-- 		                   \() -> runCont e2 k])
-- See an article on preventing memoization in search problems.

-- Generally speaking, mplus is not associative. It better not be,
-- since associative and non-commutative mplus makes the search
-- strategy incomplete.
-- Consider
--  e1 `mplus` return False >>= (\x -> if x then mzero else return x)
--   where e1 = return True `mplus` e1
-- If mplus is associative and non-commutative, the search will diverge
-- although a solution exists

-- We can now define the general choice
choose' []    = failure
choose' [x]   = return x
choose' (h:t) = return h `mplus` (choose' t)

-- A stream of numbers, more efficient that choose' [1..]
from i = choose [return i, from $! i + 1] >>= id

-- Pythagorean triples from the range of numbers

ex2 range = reify $ do
  x <- choose' range
  y <- choose' range
  z <- choose' range
  if x*x + y*y == z*z then return (x,y,z) else failure

-- Finite range
test2d = dfs $ ex2 [1..10]
-- [(3,4,5),(4,3,5),(6,8,10),(8,6,10)]

test2b = bfs $ ex2 [1..10]

-- Infinite range
-- DFS expectedly diverges, but BFS and iterative deepening give
-- solutions; iterative deepening takes much less memory than BFS.

test3d = take 5 . dfs $ ex2 [1..]
-- diverges!!

test3b = take 5 . bfs $ ex2 [1..]
-- [(3,4,5),(4,3,5),(6,8,10),(8,6,10),(5,12,13)]

test3i = take 5 . iter_deepening $ ex2 [1..]
-- [(3,4,5),(4,3,5),(6,8,10),(8,6,10),(5,12,13)]

-- Compiling it:
-- ghc -O2 -rtsopts -main-is Searches.main Searches.hs
-- To run this code
-- GHCRTS="-tstderr" ./Searches bfs  30
-- GHCRTS="-tstderr" ./Searches iter 30

ex3 = reify $ do
  x <- from 1
  y <- from 1
  z <- from 1
  if x*x + y*y == z*z then return (x,y,z) else failure

main :: IO ()
main = getArgs >>= check
 where
 check [key,ns] | [(n,"")] <- reads ns = 
   print $ take n . select key $ ex3
 select "bfs"  = bfs
 select "iter" = iter_deepening

{-
./Searches bfs 30 +RTS -tstderr 
[(3,4,5),(4,3,5),(6,8,10),(8,6,10),(5,12,13),(12,5,13),(9,12,15),(12,9,15),(8,15,17),(15,8,17),(12,16,20),(16,12,20),(7,24,25),(24,7,25),(10,24,26),(15,20,25),(20,15,25),(24,10,26),(20,21,29),(21,20,29),(18,24,30),(24,18,30),(16,30,34),(30,16,34),(12,35,37),(21,28,35),(28,21,35),(35,12,37),(9,40,41),(15,36,39)]
<<ghc: 31297248244 bytes, 59696 GCs, 289590/398080 avg/max bytes residency (15 samples), 2M in use, 0.00 INIT (0.00 elapsed), 32.39 MUT (33.12 elapsed), 19.32 GC (19.86 elapsed) :ghc>>

./Searches iter 30 +RTS -tstderr 
[(3,4,5),(4,3,5),(6,8,10),(8,6,10),(5,12,13),(12,5,13),(9,12,15),(12,9,15),(8,15,17),(15,8,17),(12,16,20),(16,12,20),(7,24,25),(24,7,25),(10,24,26),(15,20,25),(20,15,25),(24,10,26),(20,21,29),(21,20,29),(18,24,30),(24,18,30),(16,30,34),(30,16,34),(12,35,37),(21,28,35),(28,21,35),(35,12,37),(9,40,41),(15,36,39)]
<<ghc: 523312956 bytes, 999 GCs, 53842/77612 avg/max bytes residency (2 samples), 2M in use, 0.00 INIT (0.00 elapsed), 0.63 MUT (0.66 elapsed), 0.05 GC (0.05 elapsed) :ghc>>

./Searches iter 100 +RTS -tstderr 
[(3,4,5),(4,3,5),(6,8,10),(8,6,10),(5,12,13),(12,5,13),(9,12,15),(12,9,15),(8,15,17),(15,8,17),(12,16,20),(16,12,20),(7,24,25),(24,7,25),(10,24,26),(15,20,25),(20,15,25),(24,10,26),(20,21,29),(21,20,29),(18,24,30),(24,18,30),(16,30,34),(30,16,34),(12,35,37),(21,28,35),(28,21,35),(35,12,37),(9,40,41),(15,36,39),(36,15,39),(40,9,41),(24,32,40),(32,24,40),(27,36,45),(36,27,45),(14,48,50),(48,14,50),(20,48,52),(24,45,51),(30,40,50),(40,30,50),(45,24,51),(48,20,52),(28,45,53),(45,28,53),(11,60,61),(33,44,55),(44,33,55),(60,11,61),(40,42,58),(42,40,58),(16,63,65),(36,48,60),(48,36,60),(63,16,65),(25,60,65),(60,25,65),(33,56,65),(56,33,65),(39,52,65),(52,39,65),(32,60,68),(60,32,68),(21,72,75),(24,70,74),(42,56,70),(56,42,70),(70,24,74),(72,21,75),(48,55,73),(55,48,73),(18,80,82),(30,72,78),(45,60,75),(60,45,75),(72,30,78),(80,18,82),(13,84,85),(84,13,85),(48,64,80),(64,48,80),(36,77,85),(77,36,85),(40,75,85),(75,40,85),(51,68,85),(68,51,85),(39,80,89),(80,39,89),(35,84,91),(60,63,87),(63,60,87),(84,35,91),(54,72,90),(72,54,90),(20,99,101),(99,20,101),(28,96,100),(96,28,100)]
<<ghc: 19431527448 bytes, 37065 GCs, 220198/388592 avg/max bytes residency (57 samples), 2M in use, 0.00 INIT (0.00 elapsed), 23.00 MUT (23.84 elapsed), 1.56 GC (1.61 elapsed) :ghc>>

-}
