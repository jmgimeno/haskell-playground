{-
  Stack Overflow:
    is it possible to do quicksort of a list with only one passing?

    http://stackoverflow.com/questions/7641936/
-}

module QuickSort where

quickSort :: Ord a => [a] -> [a]
quickSort xs = go xs []
  where
    go     (x:xs) zs       = part x xs zs [] [] []
    go     []     zs       = zs
    part x []     zs a b c = go a ((x : b) ++ go c zs)
    part x (y:ys) zs a b c =
        case compare y x of
            LT -> part x ys zs (y:a) b c
            EQ -> part x ys zs a (y:b) c
            GT -> part x ys zs a b (y:c)
