-- Haskel.love 2020
-- Many faces of isOrderedTree (Joachim Breitner)
-- Code to the talk (extended version)
-- https://gist.github.com/nomeata/68dd80d51c2aee51ad8c97b93388c269

{-# LANGUAGE DeriveFoldable #-}
module Tree where

import Control.Monad
import Data.Maybe
import Data.Foldable

data T a = L | N (T a) a (T a) deriving (Show, Foldable)

isOrdered1 :: Ord a => T a -> Bool
isOrdered1 = everynode (\l x r -> all (<= x) (elems l) && all (>= x) (elems r))

everynode :: (T a -> a -> T a -> Bool) -> T a -> Bool
everynode p = go
  where
    go L = True
    go (N l x r) = p l x r && go l && go r

elems :: T a -> [a]
elems L = []
elems (N l x r) = elems l ++ [x] ++ elems r

-- isOrdered2 = everynode p
--   where p = …
--   inline where
--   inline p

isOrdered2 :: Ord a => T a -> Bool
isOrdered2  = go
  where
    go L = True
    go (N l x r) =
        all (<= x) (elems l) &&
        all (>= x) (elems r) &&
        go l &&
        go r

-- allElems p t = all p (elems t)
allElems :: (a -> Bool) -> T a -> Bool
allElems p L = True
allElems p (N l x r) = allElems p l && p x && allElems p r

-- replace all p elems with allElems p
isOrdered3 :: Ord a => T a -> Bool
isOrdered3 = go
  where
    go L = True
    go (N l x r) =
        allElems (<= x) l &&
        allElems (>= x) r &&
        go l &&
        go r

-- Fuse allElems and go into a single traversal
isOrdered4 :: Ord a => T a -> Bool
isOrdered4 = go' (const True)
  where
    -- go' p t = allElems p t && go t
    go' :: Ord a => (a -> Bool) -> T a -> Bool
    go' p L = True
    go' p (N l x r) =
        p x &&
        go' (\y -> p y && y <= x) l &&
        go' (\y -> p y && y >= x) r

isOrdered5 :: Ord a => T a -> Bool
isOrdered5 = go (Nothing, Nothing)
  where
    go _ L = True
    go (lb, ub) (N l x r) =
        maybe True (<= x) lb && maybe True (>= x) ub &&
        go (lb, Just x) l && go (Just x, ub) r


-- starting from isOrdered2
isOrdered6 :: Ord a => T a -> Bool
isOrdered6 t = fst (go' t)
  where
    -- go' t = (go t, elems t)
    go' :: Ord a => T a -> (Bool, [a])
    go' L = (True, [])
    go' (N l x r) =
        let (go_l, elems_l) = go' l in
        let (go_r, elems_r) = go' r in
        ( all (<= x) elems_l &&
          all (>= x) elems_r &&
          go_l &&
          go_r
        , elems_l ++ [x] ++ elems_r
        )

isOrdered7 :: Ord a => T a -> Bool
isOrdered7 t = isJust (go' t)
  where
    -- (Bool, [a]) <-> Maybe [a]
    -- (True, xs) <-> Just xs
    -- (False, _) <-> Nothing

    go' :: Ord a => T a -> Maybe [a]
    go' L = Just []
    go' (N l x r) = do
        elems_l <- go' l
        elems_r <- go' r
        guard $ all (<= x) elems_l
        guard $ all (>= x) elems_r
        return $ elems_l ++ [x] ++ elems_r

isOrdered8 :: Ord a => T a -> Bool
isOrdered8 t = isJust (go' t)
  where
    -- only check minium/maximum
    go' :: Ord a => T a -> Maybe [a]
    go' L = Just []
    go' (N l x r) = do
        elems_l <- go' l
        elems_r <- go' r
        guard $ null elems_l || maximum elems_l <= x
        guard $ null elems_r || minimum elems_r >= x
        return $ elems_l ++ [x] ++ elems_r

isOrdered9 :: Ord a => T a -> Bool
isOrdered9 t = isJust (go' t)
  where
    -- only check head/last
    go' :: Ord a => T a -> Maybe [a]
    go' L = Just []
    go' (N l x r) = do
        elems_l <- go' l
        elems_r <- go' r
        guard $ null elems_l || last elems_l <= x
        guard $ null elems_r || head elems_r >= x
        return $ elems_l ++ [x] ++ elems_r

isOrdered10 :: Ord a => T a -> Bool
isOrdered10 t = isJust (go' t)
  where
    -- [a] <-> Maybe (a,a)
    -- [] <-> Nothing
    -- [x,…,y] <-> Just (x,y)

    go' :: Ord a => T a -> Maybe (Maybe (a,a))
    go' L = Just Nothing
    go' (N l x r) = do
        elems_l <- go' l
        elems_r <- go' r
        for_ elems_l $ \(_,y) -> guard $ y <= x
        for_ elems_r $ \(y,_) -> guard $ y >= x
        return $ elems_l <.> Just (x,x) <.> elems_r

    Nothing <.> x = x
    x <.> Nothing = x
    Just (l,_) <.> Just (_,r) = Just (l,r)


-- from isOrdered6
isOrdered11 :: Ord a => T a -> Bool
isOrdered11 t = sortedList (go' t)
  where
    -- ∀ (b,xs). b = sortedList xs
    -- note dropping of Ord constraint
    go' :: T a -> [a]
    go' L = []
    go' (N l x r) = go' l ++ [x] ++ go' r

sortedList :: Ord a => [a] -> Bool
sortedList [] = True
sortedList [x] = True
sortedList (x:y:zs) = x <= y && sortedList (y : zs)

-- difference list
isOrdered12 :: Ord a => T a -> Bool
isOrdered12 t = sortedList (go' t [])
  where
    go' :: T a -> ([a] -> [a])
    go' L = id
    go' (N l x r) = go' l . (x:) . go' r

-- now use Foldable
isOrdered13 :: Ord a => T a -> Bool
isOrdered13 = sortedList . toList


-- Now testing with Quickcheck
{-
:load Tree Test ABC
:module Tree Test ABC Test.QuickCheck
quickCheck $ \t -> isOrdered1 t == isOrdered2 t
quickCheck $ \t -> isOrdered1 0 == isOrdered1 t
verboseCheck $ \t -> isOrdered1 t == isOrdered2 t
:set -XTypeApplications
verboseCheck $ \t -> isOrdered1 t == isOrdered2 @Int t
table (allFuns @Int)
:set -fobject-code -O
table (allFuns @Int)
table (allFuns @ABC)
-}