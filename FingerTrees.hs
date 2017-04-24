{-
  Finger trees: a simple general-purpose data structure
    Ralf Hinze and Ross Paterson
-}

module FingerTrees where

class Reduce f where
  reducer :: (a -> b -> b) -> f a -> b -> b
  reducel :: (b -> a -> b) -> b -> f a -> b

instance Reduce [] where
  reducer (<) x z = foldr (<) z x
  reducel (>) z x = foldl (>) z x

toList :: (Reduce f) => f a -> [a]
toList s = reducer (:) s []

data Node a = Node2 a a | Node3 a a a
  deriving Show

data FingerTree a = Empty
                  | Single a
                  | Deep (Digit a) (FingerTree (Node a)) (Digit a)
  deriving Show

type Digit a = [a]

instance Reduce Node where
  reducer (>) (Node2 a b)   z = a > (b > z)
  reducer (>) (Node3 a b c) z = a > (b > (c > z))
  reducel (<) z (Node2 b a)   = (z < b) < a
  reducel (<) z (Node3 c b a) = ((z < c) < b) < a

instance Reduce FingerTree where
  reducer (>) Empty          z = z
  reducer (>) (Single x)     z = x > z
  reducer (>) (Deep pr m sf) z = pr >> (m >>> (sf >> z))
    where (>>)  = reducer (>)
          (>>>) = reducer (reducer (>))
  reducel (<) z Empty          = z
  reducel (<) z (Single x)     = z < x
  reducel (<) z (Deep pr m sf) = ((z << pr) <<< m) << sf
    where (<<)  = reducel (<)
          (<<<) = reducel (reducel (<))

infixr 5 <|
(<|) :: a -> FingerTree a -> FingerTree a
a <| Empty               = Single a
a <| Single b            = Deep [a] Empty [b]
a <| Deep [b,c,d,e] m sf = Deep [a,b] (Node3 c d e <| m) sf
a <| Deep pr m sf        = Deep ([a] ++ pr) m sf

infixr 5 |>
(|>) :: FingerTree a -> a -> FingerTree a
Empty               |> a = Single a
Single b            |> a = Deep [b] Empty [a]
Deep pr m [e,d,c,b] |> a = Deep pr (m |> Node3 e d c) [b,a]
Deep pr m sf        |> a = Deep pr m (sf ++ [a])

(<<|) :: (Reduce f) => f a -> FingerTree a -> FingerTree a
(<<|) = reducer (<|)

(|>>) :: (Reduce f) => FingerTree a -> f a -> FingerTree a
(|>>) = reducel (|>)

toTree :: (Reduce f) => f a -> FingerTree a
toTree s = s <<| Empty

data ViewL s a = NilL | ConsL a (s a)

viewL :: FingerTree a -> ViewL FingerTree a
viewL Empty          = NilL
viewL (Single x)     = ConsL x Empty
viewL (Deep pr m sf) = ConsL (head pr) (deepL (tail pr) m sf)

deepL :: [a] -> FingerTree (Node a) -> Digit a -> FingerTree a
deepL [] m sf = case viewL m of
                  NilL       -> toTree sf
                  ConsL a m' -> Deep (toList a) m' sf
deepL pr m sf = Deep pr m sf

isEmpty :: FingerTree a -> Bool
isEmpty x = case viewL x of
              NilL      -> True
              ConsL _ _ -> False

headL :: FingerTree a -> a
headL x = case viewL x of ConsL a _ -> a

tailL :: FingerTree a -> FingerTree a
tailL x = case viewL x of ConsL _ x' -> x'

data ViewR s a = NilR | SnocR (s a) a

viewR :: FingerTree a -> ViewR FingerTree a
viewR Empty          = NilR
viewR (Single x)     = SnocR Empty x
viewR (Deep pr m sf) = SnocR (deepR pr m (init sf)) (last sf)

deepR :: Digit a -> FingerTree (Node a) -> [a] -> FingerTree a
deepR pr m [] = case viewR m of
                  NilR       -> toTree pr
                  SnocR m' a -> Deep pr m' (toList a)
deepR pr m sf = Deep pr m sf

lastR :: FingerTree a -> a
lastR x = case viewR x of SnocR _ a -> a

initR :: FingerTree a -> FingerTree a
initR x = case viewR x of SnocR x' _ -> x'
