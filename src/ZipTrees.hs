-- Thanks to davidkaste for the idea

module ZipTrees where

data Tree a = Empty | Leaf a | Root a (Tree a) (Tree a)
  deriving (Eq, Ord, Show)

instance Functor Tree where
  fmap f (Empty) = Empty
  fmap f (Leaf v) = Leaf (f v)
  fmap f (Root v left right)
    = Root (f v) (fmap f left) (fmap f right)

a = fmap (+2) (Root 10 (Leaf 4) (Empty))

instance Applicative Tree where
  pure x = Root x (pure x) (pure x)
  Empty <*> _ = Empty
  _ <*> Empty = Empty
  Leaf f <*> Leaf x = Leaf (f x)
  Leaf f <*> Root x _ _ = Leaf (f x)
  Root f _ _ <*> Leaf x = Leaf (f x)
  Root f lf rf <*> Root x lx rx = Root (f x) (lf <*> lx) (rf <*> rx)

b = (*) <$> Leaf 4 <*> Root 5 (Leaf 4) (Empty)
c = (*) <$> Root 5 (Leaf 4) (Empty) <*> Root 5 (Leaf 4) (Empty)

f = \x y z -> [x,y,z]

d = f <$> Root 1 (Leaf 2) Empty <*> Root 5 (Leaf 3) Empty <*> Root 6 (Leaf 7) (Leaf 8)
