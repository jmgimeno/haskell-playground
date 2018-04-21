---
title: "Functional pearl: Nested Datacubes"
published: 2017-04-12T18:30:00Z
tags: haskell, maps, query, aggregation, grouping, datacubes, cubes, OLAP
description: "Multi-dimensional aggregation and grouping using nested datacubes in Haskell."
---

Introduction
------------

Multi-dimensional aggregation and grouping are common forms of analysis traditionally done with SQL databases, OLAP tools (Online Analytical Processing) and/or Excel pivot tables. These traditional tools use a *flat* table representation, whereby *tuples* are mapped to *measures* without any nesting. Increasingly, users are using general purpose programming languages for further offline analysis: languages like R, Python, Scala and Haskell.  These often give us the opportunity to work with *nested* (inductive) structures, which functional languages like Haskell are particularly good at dealing with.  Hopefully this post will prove that point.


Flat versus nested
------------------

Let's start with an example flat dataset:

\

<table border="1">
  <tr><th>TradeId</th><th>Location</th><th>Date</th><th>Value</th></tr>
  <tr><td>10001</td><td>London</td><td>2017-04-01</td><td>9.99</td></tr>
  <tr><td>10003</td><td>London</td><td>2017-04-01</td><td>4.99</td></tr>
  <tr><td>10002</td><td>Shanghai</td><td>2017-04-02</td><td>86.38</td></tr>
  <tr><td>10004</td><td>Shanghai</td><td>2017-04-03</td><td>43.15</td></tr>
</table>

\

Before we model the above in Haskell, let's import some modules and define some types:

> {-# LANGUAGE ConstraintKinds #-}
> {-# LANGUAGE TypeOperators   #-}

> module Cube where

> import           Prelude            hiding (sum)
> import           Data.Foldable      (Foldable, foldMap)
> import           Data.Map           (Map)
> import qualified Data.Map           as Map
> import           Data.Monoid
> import           Data.Time.Calendar

> newtype TradeId  = TradeId  { unTradeId  :: String } deriving (Eq, Ord, Show)
> newtype Location = Location { unLocation :: String } deriving (Eq, Ord, Show)
> newtype Year  = Year  { unYear  :: Integer } deriving (Eq, Ord, Show)
> newtype Month = Month { unMonth :: Int } deriving (Eq, Ord, Show)

> data Trade = Trade
>   { tradeTradeId  :: TradeId
>   , tradeLocation :: Location
>   , tradeDate     :: Day
>   , tradeValue    :: Double
>   }

It is idiomatic in Haskell to use a nominal record type for a row, we'll call it 'Trade'.
We can then model the flat table structure above as a list of Trade: [Trade]. Even better would be to also model the uniqueness constraint using a primary key: Map TradeId Trade.

The flat structure does make a good canonical representation; and we could always add additional structures for efficiency (e.g. indexes). However, a nested representation offers quite a few advantages:

- Nesting makes grouping explicit and assigns priorities (i.e. semantics) to the different dimensions (which I concede you may or may not want). For example, a common hierarchy of dimensions are the time units: year, month and day.

- For large cubes, nesting permits efficient lookup and filtering without needing additional indexes.

- Nesting allows us to separate grouping and aggregation phases. Becuase SQL databases do not permit nested structures, they must perform grouping and aggregation in a single logical phase. This is why 'GROUP BY' needs its own 'HAVING' clause.


A better monoid instance for Data.Map
-------------------------------------

Before we create a nested dataset from the above rows, we should fix the monoid instance for Data.Map. The newtype *MMap* below has a strictly more general monoid instance. The monoid behaviour for Data.Map can be recovered by using e.g. the First Monoid from Data.Monoid. MMap deserves its own Module and qualified import, but here I'll just use the Data.Map API with explict wrapping/unwrapping to and from MMap.

Note that the complexity of unionWith is important. Unfortunately, Data.HashMap from the unordered-containers package states a complexity of O(n+m) for unionWith, which would always give us a quadratic implementation of mconcat.

> type Key = Ord

> -- A more general and useful monoid instance for maps
> newtype MMap k m = MMap { unMMap :: Map k m }

> instance Functor (MMap k) where
>     fmap f = MMap . fmap f . unMMap

> instance (Key k, Monoid m) => Monoid (MMap k m) where
>     mempty  = MMap mempty
>     -- Note the complexity of unionWith is O(m*log(n/m + 1)), m <= n
>     mappend a b = MMap $ Map.unionWith mappend (unMMap a) (unMMap b)
>     -- We must then have foldr here to get satisfactory complexity
>     mconcat = foldr mappend mempty

> instance Foldable (MMap k) where
>     foldMap f = foldMap f . unMMap


Nested groupings
----------------

To create a nested dataset, we'll need a grouping operator. GHC calls this groupWith for lists, which it uses for the generalized list comprehensions extension ([TransformListComp][TransformListComp]). It's defined in GHC.Exts and the type signature is:

~~~{.haskell}
groupWith :: Ord b => (a -> b) -> [a] -> [[a]]
~~~

Let's define an equivalent version for MMap.

> -- | Grouping for potential aggregation.
> -- Note: this implementation is sequential, but could be parallelized.
> groupWith :: (Key k, Key k') =>
>              (v -> k') -> MMap k v -> MMap k' (MMap k v)
> groupWith f = MMap . fmap MMap . Map.foldrWithKey group Map.empty . unMMap
>    where
>      group k v = Map.insertWith Map.union (f v) (Map.singleton k v)

This does require an initial MMap. A convenient choice here is: MMap TradeId Trade, which models the primary key. It is not yet a grouping, as the element can only be a single Trade record. Perhaps a more satisfiy choice, albeit less convenient in Haskell, would be to use an HList or extensible record for the keys. This would allow us to use compound-keys with various associated operations on those keys.

Let's go with groupWith and perform a grouping operation to create a level of nesting. For example, to group according to 'Location', we would use:

~~~
λ> :t groupWith tradeLocation
  :: Key k => MMap k Trade -> MMap Location (MMap k Trade)
~~~

This would group our test data into the structure shown below:

\

<table border="1">
  <tr><th>Location</th></tr>
  <tr>
    <td>London →</td>
    <td>
      <table border="1">
        <tr><th>TradeId</th><th>Date</th><th>Value</th></tr>
        <tr><td>10001 →</td><td>2017-04-01</td><td>9.99</td></tr>
        <tr><td>10003 →</td><td>2017-04-01</td><td>4.99</td></tr>
      </table>
    </td>
  </tr>
  <tr>
    <td>Shanghai →</td>
    <td>
      <table border="1">
        <tr><th>TradeId</th><th>Date</th><th>Value</th></tr>
        <tr><td>10002 →</td><td>2017-04-02</td><td>86.38</td></tr>
        <tr><td>10004 →</td><td>2017-05-03</td><td>43.15</td></tr>
      </table>
    </td>
  </tr>
</table>

\

A more satisifying 'groupWith' is perhaps the similar 'nest' operator below, which splits-up the key.
However, going down this path really does require HLists or extensible records, as nested tuples quickly get ugly.

> nest :: (Key k, Key k') =>
>         MMap (k, k') v -> MMap k (MMap k' v)
> nest = MMap . fmap MMap . Map.foldrWithKey group Map.empty . unMMap
>   where
>     group (k, k') v = Map.insertWith Map.union k (Map.singleton k' v)

Another advantage of the 'nest' grouping operator, is that it becomes easy to define the categorical dual: 'unnest'. If MMap was an 'indexed monad' it would be the [monadic join][MapComp]:

> -- the dual to nest
> unnest :: (Key k, Key k') => MMap k (MMap k' v) -> MMap (k, k') v
> unnest mm = MMap $ Map.fromList [ ((k, k'), v)
>                                 | (k, m)  <- Map.toList (unMMap mm)
>                                 , (k', v) <- Map.toList (unMMap m)
>                                 ]

With deep nestings, it becomes convenient to define an infix operator for our MMap type:

> -- | Represent mappings using a right-associated infix operator
> type k :. v = MMap k v
> infixr 8 :.

Let's now compose groupWith with fmap, to obtain grouping at various levels:

> groupWith2 :: (Key a, Key b, Key k) =>
>               (v -> k) -> a :. b :. v -> a :. k :. b :. v
> groupWith2 = fmap . groupWith

> groupWith3 :: (Key a, Key b, Key c, Key k) =>
>               (v -> k) -> a :. b :. c :. v -> a :. b :. k :. c :. v
> groupWith3 = fmap . fmap . groupWith

Using the above grouping operators, we can now obtain nested groupings, such as 'timeDimensions' below. However, such an API can difficult to use. We need to keep track of the type (level of nesting) within the expression. This could get awkward, once we start including aggregations.

~~~{.haskell}
timeDimensions :: (Key k) => MMap k Trade
               -> Year :. Month :. Day :. k :. Trade
timeDimensions = groupWith3 tradeDate
               . groupWith2 (month . tradeDate)
               . groupWith  (year  . tradeDate)
~~~

A nice alternative, is to define a grouping function that also applies a function parameter to each resultant group:

> -- | An alternative grouping function which can optionally aggregate
> -- or further group each resultant group.
> groupBy :: (Key k, Key k') =>
>            (v -> k') -> (MMap k v -> v') -> MMap k v -> MMap k' v'
> groupBy f g = fmap g . groupWith f

This function parameter can be another grouping operation, to perform at the next level of nesting. We can then therefore compose 'groupBy' to get a very readable (positional) definition of a grouping:

> timeDimensions  :: (Key k) => (k :. Trade -> m)
>                 -> k :. Trade
>                 -> Year :. Month :. Day :. m
> timeDimensions = groupBy (year  . tradeDate)
>                . groupBy (month . tradeDate)
>                . groupBy tradeDate

Such definitions are easily composed further, without worrying about the level of nesting (let GHC figure out the type!).

> myCube :: (Key k) => (k :. Trade -> m)
>        -> k :. Trade
>        -> Location :. Year :. Month :. Day :. m
> myCube = groupBy tradeLocation
>        . timeDimensions

Of course, our grouping/cube definitions above still do not actually do any aggregation. They remain parameterized with a function to apply to the inner-most level of nesting.


Aggregation
-----------

To aggregate, we need to fold or reduce the elements (possibly inner groupings) of a map into a single value (not necessarily an atomic value). The function we need is 'foldMap', but I'm going to create a new fancy name for it:

> rollup :: (Monoid m) => (v -> m) -> MMap a v -> m
> rollup = foldMap

Now we have the necessary operator to rollup the innermost grouping of our cube:

> myCubeSum :: (Key k) => k :. Trade
>           -> Location :. Year :. Month :. Day :. Sum Double
> myCubeSum = myCube (rollup $ Sum . tradeValue)

Applying the above aggregation 'myCubeSum' to our test data (of type 'MMap TradeId Trade'), would yield the following structure:

\

<table border="1">
  <tr><th>Location</th></tr>
  <tr>
    <td>London →</td>
    <td>
      <table border="1">
         <tr><th>Year</th></tr>
         <tr>
           <td>2017 →</td>
           <td>
             <table border="1">
               <tr><th>Month</th></tr>
               <tr>
               <td>04 →</td>
               <td>
                 <table border="1">
                 <tr><th>Day</th><th>Value</th></tr>
                 <tr><td>2017-04-01 →</td><td>14.98</td></tr>
                 </table>
               </td>
             </table>
           </td>
      </table>
    </td>
  </tr>
  <tr>
    <td>Shanghai →</td>
    <td>
      <table border="1">
         <tr><th>Year</th></tr>
         <tr>
           <td>2017 →</td>
           <td>
             <table border="1">
               <tr><th>Month</th></tr>
               <tr>
                 <td>04 →</td>
                 <td>
                   <table border="1">
                   <tr><th>Day</th><th>Value</th></tr>
                   <tr><td>2017-04-02</td><td>86.38</td></tr>
                   </table>
                 </td>
               </tr>
               <tr>
                 <td>05 →</td>
                 <td>
                   <table border="1">
                   <tr><th>Day</th><th>Value</th></tr>
                   <tr><td>2017-05-03</td><td>43.15</td></tr>
                   </table>
                 </td>
               </tr>
             </table>
           </td>
         </tr>
      </table>
    </td>
  </tr>
</table>

\

Note that aggregations can have types that look similar to unnesting/ungrouping, but of course they do not form isomorphisms with our grouping operators. In general, we cannot undo an aggregation.

> -- the type looks similar to unnest, but this function aggregates!
> rollup1 :: (Monoid m, Key k, Key k') => (v -> m) -> MMap k (MMap k' v) -> MMap k m
> rollup1 = fmap . foldMap


Parallel Aggregation
--------------------

Since MMap has the general monoid instance we defined earlier, our cube aggregations will also all have monoid instances (by induction).
This means we can compute partial cubes for input chunks in parallel and then mconcat/reduce them to obtain the final cube.

> mapReduce :: (Monoid m) => (v -> m) -> [v] -> m
> mapReduce f = mconcat . map f -- parallel map

~~~{.haskell}
λ> :t mapReduce myCubeSum
mapReduce myCubeSum
  :: Key k =>
     [k :. Trade]
     -> Location :. Year :. Month :. Day :. Sum Double
~~~


Subcubes
--------

I'm using the word "subcube" here to describe cubes built from aggregating larger/deeper grouping definitions.

Instead of creating a series of operators to aggregate over each successive level of nesting, we will use a positional style, as we did with the grouping definitions.

First, let's create a new name for fmap:

> keep :: (Monoid m) => (v -> m) -> MMap a v -> MMap a m
> keep = fmap

We can now just specify in the term, what we want to happen to each dimension as it appears in the type. For example to rollup just the Year and Month, we can write the following:

> -- a "subcube" definition, parameterized by an aggregation function
> locationByMonth :: (Monoid m) => (v -> m)
>                 -> Location :. Year :. Month :. Day :. v
>                 -> Location :. Month :. m
> locationByMonth = keep . rollup . keep . rollup

I think the above is rather nice!

\

Note: the literal haskell for this entire post can be found [here](https://raw.githubusercontent.com/willtim/timphilipwilliams.com/master/posts/2017-04-12-nested-datacubes.lhs).

* * * * * * * *

References
----------

\[1\] [Map Comprehensions][MapComp]

\[2\] [TransformListComp][TransformListComp]

[MapComp]: 2014-06-05-map-comprehensions.html (Map Comprehensions)
[TransformListComp]: https://downloads.haskell.org/~ghc/8.0.1/docs/html/users_guide/glasgow_exts.html#generalised-sql-like-list-comprehensions (Generalised (SQL-like) List Comprehensions)

\


Appendix
--------

<h4>Auxiliary functions</h4>

> year :: Day -> Year
> year d = let (y, _, _) = toGregorian d in Year y

> month :: Day -> Month
> month d = let (_, m, _) = toGregorian d in Month m
