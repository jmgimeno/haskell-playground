-- An illustration of simple delimited control in Haskell,
-- in the Cont monad and ContT monad transformer
-- for delimited control

-- Requirements: Cont monad or ContT transformer from
-- the monad transformer library such as mtl
-- The examples below use mtl-1.1.1.0 (and a newer mtl 2.x)
-- Please install it from Hackage

module ContExample where

import Control.Monad.Cont

-- shift/reset in the Cont monad

runC :: Cont w w -> w
runC m = runCont m id

reset :: Cont a a -> Cont w a
reset = return . runC

shift :: ((a -> w) -> Cont w w) -> Cont w a
-- for new mtl 2.x
shift f = cont (runC . f)
-- For the old mtl 1.x
-- shift f = Cont (runC . f)

-- The first running example
-- 1 + reset (2 * shift (fun k -> k (k 10)))

ex1 :: Cont Int Int
ex1 = liftM2 (+) (return 1)
        (reset $ 
          liftM2 (*) (return 2)
            (shift $ \k -> return $ k (k 10)))

ex1r = runC ex1
-- 41


-- shift/reset in the ContT monad transformer

runCT :: Monad m => ContT w m w -> m w
runCT m = runContT m return

resetT :: Monad m => ContT a m a -> ContT w m a
resetT = lift . runCT

shiftT :: Monad m => ((a -> m w) -> ContT w m w) -> ContT w m a
shiftT f = ContT (runCT . f)

-- Same-fringe problem for a binary tree

data Tree = Empty | Node Tree Int Tree deriving Show

make_complete :: Int -> Tree
make_complete d = go d 1
 where
 go 0 _ = Empty
 go d n = Node (go (d-1) (2*n)) n (go (d-1) (2*n+1))

-- Sample trees
tree1 = make_complete 3
tree2 = make_complete 4


-- Printing the tree
print_tree:: Tree -> IO ()
print_tree Empty        = return ()
print_tree (Node l n r) = do
  print_tree l
  putStrLn $ "walked to " ++ show n
  print_tree r
			 

-- How to `capture' the result of the printing?
-- In addition to printing the nodes, we also wish
-- to return them in a list -- lazy list.


-- Co-routines
-- Thread m a is isomorphic to a list with a monadic tail
data Thread m a = Done | Resume a (m (Thread m a))



-- Walking with the debug printing
-- (that's why we use MonadIO: to print out the trace)
walk_tree:: MonadIO m => Tree -> m (Thread m Int)
walk_tree t = runCT (walk_tree' t >> return Done)

walk_tree':: MonadIO m => Tree -> ContT (Thread m Int) m ()
walk_tree' Empty        = return ()
walk_tree' (Node l n r) = do
   walk_tree' l
   liftIO $ putStrLn $ "walked to " ++ show n
   yield n
   walk_tree' r
  where yield n = shiftT (\k -> return $ Resume n (k ()))
			 

-- Sample walking

walk1 :: IO ()
walk1 = walk_tree tree1 >>= check
 where check Done = return ()
       check (Resume n r) = do
                            putStrLn $ "found " ++ show n
			    r >>= check

{-
*Cont> walk1
walked to 4
found 4
walked to 2
found 2
walked to 5
found 5
walked to 1
found 1
walked to 6
found 6
walked to 3
found 3
walked to 7
found 7
-}

-- Same fringe: walking two trees side-by-side

same_fringe :: Tree -> Tree -> IO ()
same_fringe t1 t2 = ap2 check (walk_tree t1) (walk_tree t2) 
 where
 check Done Done = putStrLn "*** The same ***"
 check (Resume n _) Done = 
   putStrLn $ unwords ["First tree", show n, "second is empty"]
 check Done (Resume n _) = 
   putStrLn $ unwords ["Second tree", show n, "first is empty"]
 check (Resume n1 _) (Resume n2 _) | n1 /= n2 =
   putStrLn $ unwords ["First tree", show n1, "second tree", show n2]
 check (Resume n1 r1) (Resume n2 r2) = ap2 check r1 r2
 ap2 f x y = x >>= \x' -> y >>= \y' -> f x' y'

sf1 = same_fringe tree1 tree1

-- The trace shows that the traversal terminated right away
sf2 = same_fringe tree1 tree2
{-
*Cont> sf2
walked to 4
walked to 8
First tree 4 second tree 8
-}
