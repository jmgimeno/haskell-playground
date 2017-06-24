{-# LANGUAGE PatternGuards #-}

-- Demonstrating that a Zipper can be derived from any Traversable
-- Haskell-Cafe, March 31, 2009

-- We use Data.Map as a sample Traversable data structure to turn
-- into a Zipper. That is a bit silly since Data.Map has a very
-- rich interface; it does not need zippers.
-- However, Data.Map is the only non-trivial instance of Traversable
-- defined in the standard library.

module ZipperTraversable where

import qualified Data.Traversable as T
import qualified Data.Map as M


-- In the variant Z a k, a is the current, focused value
-- evaluate (k Nothing) to move forward
-- evaluate (k v)       to replace the current value with v and move forward.

data Zipper t a = ZDone (t a)
                | Z a (Maybe a -> Zipper t a)

make_zipper :: T.Traversable t => t a -> Zipper t a
make_zipper t = reset $ T.mapM f t >>= return . ZDone
 where
 f a = shift (\k -> return $ Z a (k . maybe a id))

-- Zip all the way up, returning the traversed data structure
zip_up :: Zipper t a -> t a
zip_up (ZDone t) = t
zip_up (Z _ k)   = zip_up $ k Nothing



-- Tests

-- sample collections

tmap = M.fromList [ (v,product [1..v]) | v <- [1..10] ]

-- extract a few sample elements from the collection
trav t =
    let (Z a1 k1) = make_zipper t
        (Z a2 k2) = k1 Nothing
        (Z a3 k3) = k2 Nothing
        (Z a4 k4) = k3 Nothing
     in [a1,a3,a4]

travm = trav tmap

-- Traverse and possibly modify elements of a collection
tmod t = loop (make_zipper t)
 where
 loop (ZDone t) = putStrLn $ "Done\n: " ++ show t
 loop (Z a k) = do
                putStrLn $ "Current element: " ++ show a
                ask k

 ask k =        do
                putStrLn "Enter Return, q or the replacement value: "
                getLine >>= check k

 check k ""   = loop $ k Nothing
 check k "\r" = loop $ k Nothing
 check k ('q':_) = loop . ZDone . zip_up $ k Nothing
 check k s  | [(n,_)] <- reads s = loop $ k (Just n) -- replace
 check k _    = putStrLn "Repeat" >> ask k

testm = tmod tmap


-- The Cont monad for delimited continuations, implemented here to avoid
-- importing conflicting monad transformer libraries

newtype Cont r a = Cont { runCont :: (a -> r) -> r }

instance Monad (Cont r) where
    return x = Cont $ \k -> k x
    m >>= f  = Cont $ \k -> runCont m (\v -> runCont (f v) k)

-- Two delimited control operators,
-- without answer-type polymorphism or modification
-- These features are not needed for the application at hand

reset :: Cont r r -> r
reset m = runCont m id

shift :: ((a -> r) -> Cont r r) -> Cont r a
shift e = Cont (\k -> reset (e k))
