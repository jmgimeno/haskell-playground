{-# LANGUAGE DeriveFunctor #-}

{-

Comonad, Zipper and Conway's Game of Life (Part 2)

http://javran.github.io/posts/2014-08-22-comonad-zipper-and-conways-game-of-life.html

-}

module CA.LZipper where

-- | LZipper <current> <left (reversed)> <right>
data LZipper a = LZipper a [a] [a]
    deriving (Show, Functor)

-- | shift left and right
zipperMoveL, zipperMoveR :: LZipper a -> LZipper a
zipperMoveL (LZipper a (x:xs') ys) = LZipper x xs' (a:ys)
zipperMoveL _ = error "Invalid move"
zipperMoveR (LZipper a xs (y:ys')) = LZipper y (a:xs) ys'
zipperMoveR _ = error "Invalid move"

-- | get the current focusing element
current :: LZipper a -> a
current (LZipper v _ _) = v

-- | initial world to a zipper
rangeToZipper :: a -> [a] -> LZipper a
rangeToZipper v wd = case wd of
    []   -> LZipper v pad pad
    x:xs -> LZipper x pad (xs ++ pad)
    where
        pad = repeat v

-- | a view range (coordinates), a zipper to a portion of the world
zipperToRange :: (Int, Int) -> LZipper a -> [a]
zipperToRange (i,j) zp = fmap current zippers
    where
        zippers = take (j - i + 1) (iterate zipperMoveR startZ)
        startZ = zipperMoveFocus i zp
        zipperMoveFocus :: Int -> LZipper a -> LZipper a
        zipperMoveFocus t z
            | t > 0     = zipperMoveFocus (t-1) (zipperMoveR z)
            | t < 0     = zipperMoveFocus (t+1) (zipperMoveL z)
            | otherwise = z

waveRule :: LZipper Char -> Char
waveRule (LZipper _ (l:_) (r:_))
    | fromL && fromR = 'X'
    | fromL          = '>'
    | fromR          = '<'
    | otherwise      = ' '
    where
        fromL = l `elem` ">*X"
        fromR = r `elem` "<*X"
waveRule _ = error "null zipper"

nextGen :: LZipper Char -> LZipper Char
nextGen z = LZipper c' ls' rs'
    where
        c' = waveRule z
        -- keep moving the zipper to its left or right
        -- apply `waveRule` to get next cell states
        ls' = map waveRule . tail $ iterate zipperMoveL z
        rs' = map waveRule . tail $ iterate zipperMoveR z

main :: IO ()
main = mapM_ (putStrLn . zipperToRange (-20,40)) (take 20 (iterate nextGen startZ))
    where
        startStr = "*  >  *   *  <  **<"
        startZ = rangeToZipper ' ' startStr
