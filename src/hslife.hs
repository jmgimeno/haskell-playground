{-

  HSLIFE: a Haskell implementation of hashlife.

  This was written by Tony Finch <dot@dotat.at>.
  You may do anything with it, at your own risk.

  $dotat: life/hslife.hs,v 1.36 2008/04/10 13:31:06 fanf2 Exp $

-}

------------------------------------------------------------------------

{-  INTRODUCTION  -}

-- Hashlife is a radically powerful way of computing Conway's Game of
-- Life. It was invented by Bill Gosper who originally described it in
-- his 1984 paper "Exploiting Regularities in Large Cellular Spaces",
-- Physica D (Nonlinear Phenomena) volume 10 pp. 75-80.
--
-- It uses several cunning techniques:
--
-- The universe is represented as a quadtree of nested squares that
-- are powers of two cells on a side. There is an intricate and
-- beautiful recursive function for computing the Game of Life using
-- this data structure.
--
-- It avoids constructing multiple copies of equivalent portions of
-- the universe that are duplicated at different places or times by
-- looking up previously-constructed squares in the eponymous hash
-- table. (This technique is sometimes known as hash-consing.) It also
-- uses hash tables to avoid repeating Game of Life computations and
-- population counts.
--
-- Because of its aggressive memoization it is extremely effective at
-- computing Life patterns that have some kind of repetition in space
-- or time. Hashlife can take the same length of time to compute from
-- generation N to generation 2N for any large enough N - it has
-- logarithmic complexity. Its disadvantage is that it is not very
-- fast at handling random Life soup.
--
-- There are a few hashlife resources on the web. You can get David
-- Bell's implementation from <http://members.pcug.org.au/~dbell/>.
-- Tomas Rokicki's implementation is part of the "Golly" Game of Life
-- simulator <http://golly.sourceforge.net/> and he also wrote about
-- it for Dr Dobb's: "An Algorithm for Compressing Space and Time"
-- <http://www.ddj.com/hpc-high-performance-computing/184406478>.
-- For an example of hashlife's capabilities, computing 2^130
-- generations of the Metacatacryst producing a pattern of 2^232
-- cells, see <http://tomas.rokicki.com/mcc/>.
-- I first read about hashlife when working on my previous (more
-- conventional) Life implementation, which can be found at
-- <http://dotat.at/prog/misc/life.html>. I also have part of a
-- C version of hashlife, along the same lines as this code, at
-- <http://dotat.at/prog/misc/hashlife.c>.

import qualified Data.HashTable as HT
import           Data.Int
import           Graphics.UI.GLUT
import           System.Exit ( exitWith, ExitCode(ExitSuccess) )
import           System.IO.Unsafe
import           System.Mem.StableName
import           System.Mem.Weak

------------------------------------------------------------------------

{-  HASH CONSING AND MEMOISATION  -}

-- It is impossible to implement hash-consing and memoization in
-- standard Haskell, because to do so generally requires some notion
-- of pointer equality. Fortunately, the Glasgow Haskell Compiler has
-- some advanced features that fill this gap. The details can be found
-- in the paper "Stretching the storage manager: weak pointers and
-- stable names in Haskell" by Simon Peyton Jones, Simon Marlow, and
-- Conal Elliott, published in the proceedings of the Workshop on
-- Implementing Functional Languages, 1999, and on the web at
-- http://research.microsoft.com/~simonpj/Papers/weak.htm
--
-- (One consequence of using this technology is a bit irritating.
-- Although Glasgow Parallel Haskell ought to make it easy to run
-- a Haskell program on multiple CPUs, it does not support the
-- StableName API, so this code cannot be parallelized.)
--
-- Memoisation and hash-consing are sort-of duals: memoising spends
-- memory to save time, and hash-consing spends time to save memory.
-- Accordingly, the memo function in the paper keeps its results in
-- memory as long as the corresponding arguments are still reachable
-- and may therefore be used again. This would be catastrophic for a
-- hash-cons function, since it would cause the higher levels of the
-- data structure to be retained as long as the lower levels are
-- reachable, thereby defeating the garbage collector. (In our code
-- the lowest levels of the data structure are always reachable for
-- reasons explained below.) Therefore a hash-cons function uses
-- mkWeakPtr where a memo function uses mkWeak.
--
-- As a slight simplification, we don't bother with the paper's mechanism
-- for garbage-collecting whole hash tables, because our tables will exist
-- for the life of the program because of the permanent reachability of
-- their low-level members.
--
-- So now for the nuts and bolts.
--
-- The hash-cons table maps a quad to the canonical version of the
-- square containing that quad. It identifies quads by the stable
-- names of their constituent squares. (We don't care about the
-- identity in memory of the quad itself, since quads are often
-- re-created to be passed around.) The canonical square is wrapped
-- in a weak pointer so that it can be destroyed when it is no
-- longer needed.

type MemoTable name val = HT.HashTable name (Weak val)

type HashConsTable = MemoTable (Quad (StableName Square)) Square
type CalcHashTable = MemoTable (StableName Square) Square
type PopHashTable  = MemoTable (StableName Square) Integer

makeStableName4 :: Quad a -> IO (Quad (StableName a))
makeStableName4 (nw,ne,sw,se) = do
    nwn <- makeStableName nw
    nen <- makeStableName ne
    swn <- makeStableName sw
    sen <- makeStableName se
    return (nwn,nen,swn,sen)

-- To hash a quad, we must combine the hashes of its constituent
-- stable names non-commutatively so that quads with the same
-- elements in different orders hash differently. Annoyingly,
-- hashStableName returns an Int but HashTable wants Int32.

hashStableName4 :: Quad (StableName a) -> Int32
hashStableName4 (nw,ne,sw,se) =
    fromIntegral (nwh*3 + neh*5 + swh*7 + seh*9)
  where
    nwh = hashStableName nw
    neh = hashStableName ne
    swh = hashStableName sw
    seh = hashStableName se

makeStableName4' :: (Int, Integer, Quad a)
                 -> IO (Integer, Quad (StableName a))
makeStableName4' (lev,gen,q) = do
    qsn <- makeStableName4 q
    return (gen,qsn)

hashStableName4' :: (Integer, Quad (StableName a)) -> Int32
hashStableName4' (n,q) = fromIntegral n + hashStableName4 q

-- The core of our hash-cons function is essentially the same as the
-- memo function from the paper referenced above. The bare function
-- isn't ideal since we don't want to have to pass the hash table
-- around everywhere. Instead we use the helper function below to
-- create the hash table once when the program starts, and partially
-- apply find'' to it yielding find'. The constructor functions in the
-- hashlife code below are defined using find'.

memoize :: MemoTable name val -> (key -> IO name) -> (key -> IO val)
        -> key -> IO val
memoize tbl mkname mkval key = do
    sn <- mkname key
    found <- HT.lookup tbl sn
    case found of
      Nothing -> cons sn
      Just ptr -> do
        maybe <- deRefWeak ptr
        case maybe of
          Nothing -> cons sn
          Just val -> return val
  where
    cons sn = do
      let gc = HT.delete tbl sn
      val <- mkval key
      wp <- mkWeak key val (Just gc)
      HT.insert tbl sn wp
      return val

-- The code below relies on the hashcons table to provide the base
-- case of the hashlife recursion, by using a different non-recursive
-- calculation function for the lowest-level squares instead of
-- repeatedly testing for the bottom in the main loop. In order for
-- this to work, the bottom squares must be constructed before the
-- recursive calculation is invoked and they must never be destroyed,
-- otherwise they might be (re)constructed with a calculator that
-- recurses into undefined territory. To achieve this, the bottom
-- squares are stored in global lists, which prevents them from being
-- destroyed, and the main program ensures that they are fully
-- constructed before anything else is done with the data structure.

memoins :: MemoTable name val -> (key -> IO name) -> key -> val -> IO ()
memoins tbl mkname key val = do
    sn <- mkname key
    wp <- mkWeak key val Nothing
    HT.insert tbl sn wp

------------------------------------------------------------------------

{-  CORE DATA STRUCTURE AND ALGORITHM  -}

-- Hashlife divides the universe up into a quadtree. A square at
-- level n is 2^n cells on a side, and divided into four level n-1
-- quarters with half as many cells on a side, i.e. 2^(n-1). We do
-- not need to store the level explicitly since we can keep track
-- of it by counting depth of recursion.  The code is written
-- consistently to handle sub-squares in reading order named by
-- diagonal compass points, NW, NE, SW, SE.

type Quad a = (a,a,a,a)
newtype Square = Square (Quad Square)

-- The accessor functions for a square's sub-squares are defined via a
-- projection operator, which is named after ML's built-in projection
-- operator. It has the same precedence as the list index operator !!

infixl 9 #

data SubSquare = NW | NE | SW | SE

(#) :: Square -> SubSquare -> Square
Square (nw,ne,sw,se) # NW = nw
Square (nw,ne,sw,se) # NE = ne
Square (nw,ne,sw,se) # SW = sw
Square (nw,ne,sw,se) # SE = se

type SquarePop = Square -> IO Integer
type SquareCons = Quad Square -> IO Square
type SquareCalc = Int -> Integer -> Square -> IO Square

-- There are two level 0 squares, each being one cell that is dead or
-- alive, as determined by its population. They have no sub-squares
-- and they are too small for us to compute their future, so we leave
-- those fields of the square undefined. Read "sq_0" as "squares at
-- level 0".

dead, alive :: Square
dead  = Square (dead,dead,dead,dead)
alive = Square (alive,alive,alive,alive)

sq_0, sq_1, sq_2 :: [Square]
sq_0 = [ dead, alive ]
sq_1 = [ Square (nw,ne,sw,se)
       | nw <- sq_0, ne <- sq_0, sw <- sq_0, se <- sq_0 ]
sq_2 = [ Square (nw,ne,sw,se)
       | nw <- sq_1, ne <- sq_1, sw <- sq_1, se <- sq_1 ]

-- The state of a cell in the next generation is determined by its
-- current state and the number of its neighbours that are alive,
-- according to the rules invented by Conway. In the following
-- function, the squares are at level 0, i.e. they are cells.

calc_3x3 :: SquarePop -> Square -> Square -> Square
                      -> Square -> Square -> Square
                      -> Square -> Square -> Square -> IO Square
calc_3x3 pop nw nn ne
             ww cc ee
             sw ss se = do
    pnw <- pop nw;  pnn <- pop nn;  pne <- pop ne;
    pww <- pop ww;                  pee <- pop ee;
    psw <- pop sw;  pss <- pop ss;  pse <- pop se;
    let count = pnw + pnn + pne
              + pww       + pee
              + psw + pss + pse
    return $ if count == 2 then  cc   else
             if count == 3 then alive else dead

calc_4x4 :: SquareCons -> SquarePop -> Quad Square -> IO Square
calc_4x4 cons pop (nw,ne,sw,se) = do
    nwr <- calc_3x3 pop (nw#NW) (nw#NE) (ne#NW)
                        (nw#SW) (nw#SE) (ne#SW)
                        (sw#NW) (sw#NE) (se#NW)
    ner <- calc_3x3 pop (nw#NE) (ne#NW) (ne#NE)
                        (nw#SE) (ne#SW) (ne#SE)
                        (sw#NE) (se#NW) (se#NE)
    swr <- calc_3x3 pop (nw#SW) (nw#SE) (ne#SW)
                        (sw#NW) (sw#NE) (se#NW)
                        (sw#SW) (sw#SE) (se#SW)
    ser <- calc_3x3 pop (nw#SE) (ne#SW) (ne#SE)
                        (sw#NE) (se#NW) (se#NE)
                        (sw#SE) (se#SW) (se#SE)
    cons (nwr,ner,swr,ser)

------------------------------------------------------------------------

get_nw cons (nw,ne,sw,se) = return nw
get_nn cons (nw,ne,sw,se) = cons (nw#NE, ne#NW, nw#SE, ne#SW)
get_ne cons (nw,ne,sw,se) = return ne
get_ww cons (nw,ne,sw,se) = cons (nw#SW, nw#SE, sw#NW, sw#NE)
get_cc cons (nw,ne,sw,se) = cons (nw#SE, ne#SW, sw#NE, se#NW)
get_ee cons (nw,ne,sw,se) = cons (ne#SW, ne#SE, se#NW, se#NE)
get_sw cons (nw,ne,sw,se) = return sw
get_ss cons (nw,ne,sw,se) = cons (sw#NE, se#NW, sw#SE, se#SW)
get_se cons (nw,ne,sw,se) = return se

calc' :: SquareCons -> SquareCalc -> SquareCalc
calc' cons rec lev gen (Square q) =
  let
    half = 2^(lev - 3)
    rec' = rec (lev - 1)
    gen' = gen - half
    rec1 :: Square -> IO Square
    rec2 :: Quad Square -> IO Square
    rec1 = if gen < half then rec' gen else rec' half
    rec2 q = if gen > half then cons q >>= rec' gen' else get_cc cons q
  in do
    nw1 <- rec1 =<< get_nw cons q
    nn1 <- rec1 =<< get_nn cons q
    ne1 <- rec1 =<< get_ne cons q
    ww1 <- rec1 =<< get_ww cons q
    cc1 <- rec1 =<< get_cc cons q
    ee1 <- rec1 =<< get_ee cons q
    sw1 <- rec1 =<< get_sw cons q
    ss1 <- rec1 =<< get_ss cons q
    se1 <- rec1 =<< get_se cons q
    nw2 <- rec2 (nw1, nn1, ww1, cc1)
    ne2 <- rec2 (nn1, ne1, cc1, ee1)
    sw2 <- rec2 (ww1, cc1, sw1, ss1)
    se2 <- rec2 (cc1, ee1, ss1, se1)
    cons (nw2, ne2, sw2, se2)

pop' :: SquarePop -> SquarePop
pop' rec (nw,ne,sw,se) = do
    nwp <- rec nw
    nep <- rec ne
    swp <- rec sw
    sep <- rec se
    return $ nwp + nep + swp + sep

init_pop :: IO SquarePop
init_pop = do
    tbl <- HT.new (==) hashStableName4
    memoins tbl makeStableName4 dead 0
    memoins tbl makeStableName4 alive 1
    let pop = memoize tbl makeStableName4 (pop' pop)
    return pop

init_cons :: IO SquareCons
init_cons = do
    tbl <- HT.new (==) hashStableName4
    let add q = memoins tbl makeStableName4 q q
    mapM_ add (sq_0 ++ sq_1 ++ sq_2)
    return $ memoize tbl makeStableName4 return

init_calc :: SquareCons -> SquarePop -> IO SquareCalc
init_calc cons pop = do
    tbl <- HT.new (==) hashStableName4'
    let add q = memoins tbl makeStableName4' (2,1,q) (calc_4x4 cons pop q)
    mapM_ add sq_2
    let calc lev gen q = memoize tbl makeStableName4' calc'' (lev,gen,q)
        calc'' (lev,gen,q) = calc' cons calc lev gen q
    return calc

------------------------------------------------------------------------
