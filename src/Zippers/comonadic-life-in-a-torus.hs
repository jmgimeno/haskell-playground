--
-- Comonadic Life on a Torus
--
-- Code by NOTtheMessiah, built entirely upon
-- http://blog.emillon.org/posts/2012-10-18-comonadic-life.html
-- 
-- Taking the antiderivative of the loop zipper as if it were a GADT
-- yields -log(1-x) which has a series expansion  sum [a^n / n | n <- [0..]]
-- which seemingly indicates (x^3) / 3 represents [a,b,c]=[b,c,a]=[c,a,b]
-- as of now, I know of no such data type.
--

import Control.Comonad
import Control.Monad

data LoopZipper a = LZ a [a] deriving Show

loopLeft :: LoopZipper a -> LoopZipper a
loopLeft (LZ a b) = LZ (last b) (a : init b)
loopLeft _ = error "loopLeft"

loopRight :: LoopZipper a -> LoopZipper a
loopRight (LZ a b) = LZ (head b) (tail b ++ [a])
loopRight _ = error "loopRight"

loopRead :: LoopZipper a -> a
loopRead (LZ x _) = x

loopWrite :: a -> LoopZipper a -> LoopZipper a
loopWrite x (LZ _ rs) = LZ x rs

toList :: LoopZipper a -> [a]
toList (LZ x rs) = x : rs

loopLength (LZ a b) = 1 + length b

instance Functor LoopZipper where
  fmap f (LZ x rs) = LZ (f x) (map f rs)


genericMove :: (z a -> z a)
            -> (z a -> z a)
            -> z a
            -> LoopZipper (z a)
genericMove a b z = LZ z (iterate' b z)

iterate' :: (a -> a) -> a -> [a]
iterate' f = tail . iterate f

iterateN :: Int -> (a -> a) -> a -> [a]
iterateN n f = take n . tail . iterate f

genericMoveFinite l f a = LZ a $iterateN (l a) f a 

instance Comonad LoopZipper where
  extract = loopRead
  duplicate = genericMoveFinite (pred.loopLength) loopRight

data Z a = Z (LoopZipper (LoopZipper a))

up :: Z a -> Z a
up (Z z) = Z (loopLeft z)

down :: Z a -> Z a
down (Z z) = Z (loopRight z)

left :: Z a -> Z a
left (Z z) = Z (fmap loopLeft z)

right :: Z a -> Z a
right (Z z) = Z (fmap loopRight z)

torusShape (Z a) = (loopLength a, extract $fmap loopLength a)

zRead :: Z a -> a
zRead (Z z) = loopRead $ loopRead z

zWrite :: a -> Z a -> Z a
zWrite x (Z z) =
  Z $ loopWrite newLine z
    where
      newLine = loopWrite x oldLine
      oldLine = loopRead z

instance Functor Z where
  fmap f (Z z) = Z (fmap (fmap f) z)

horizontal :: Z a -> LoopZipper (Z a)
horizontal = genericMoveFinite (pred.fst.torusShape) right

vertical :: Z a -> LoopZipper (Z a)
vertical = genericMoveFinite (pred.snd.torusShape) down

instance Comonad Z where
  extract = zRead
  duplicate z =
    Z $ fmap horizontal $ vertical z

neighbours :: [Z a -> Z a]
neighbours =
  horiz ++ vert ++ liftM2 (.) horiz vert
    where
      horiz = [left, right]
      vert  = [up, down]

aliveNeighbours :: Z Bool -> Int
aliveNeighbours z =
  card $ map (\ dir -> extract $ dir z) neighbours

card :: [Bool] -> Int
card = length . filter (==True)

rule :: Z Bool -> Bool
rule z =
  case aliveNeighbours z of
    2 -> extract z
    3 -> True
    _ -> False

evolve :: Z Bool -> Z Bool
evolve = extend rule

dispLine :: LoopZipper Bool -> String
dispLine z =
  map dispC $ toList z
    where
      dispC True  = '*'
      dispC False = ' '

disp :: Z Bool -> String
disp (Z z) =
  unlines $ map dispLine $ toList z

glider :: Z Bool
glider =
  Z $ LZ fz rs
    where
      rs = [ line [f, t, f]
           , line [f, f, t]
           , line [t, t, t]
           ] ++ replicate 9 fz
      t = True
      f = False
      fz = LZ f (replicate 12 f)
      line l =
        LZ f (l ++ replicate 9 f)

main = do
  putStr.disp $ glider
  putStr.disp $ evolve $ glider
  putStr.disp $ evolve.evolve $ glider
  putStr.disp $ evolve.evolve.evolve $ glider
  putStr.disp $ evolve.evolve.evolve.evolve $ glider