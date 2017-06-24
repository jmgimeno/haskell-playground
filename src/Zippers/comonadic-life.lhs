---
title: Comonadic Life
author: Etienne Millon
tags: haskell, conway, life, comonad, algebra
---

Of monads and comonads
----------------------

This post is written in [Literate Haskell]. This means that you can copy it into
a `.lhs` file[^1] and run it through a Haskell compiler or interpreter.

[^1]: Or download the [source on github].

Today we'll talk about…

> import Control.Comonad
> import Control.Monad

Comonads ! They are the categoric dual of monads, which means that the type
signatures of comonadic functions look like monadic functions, but with the
arrow reversed. I am not an expert in category theory, so I won't go further.

I will use the following typeclass for comonads : it's from [Edward Kmett]'s
[comonad package] (split from the infamous [category-extras package]).

~~~~ {.haskell}
class Functor w => Comonad w where
  extract :: w a -> a
  extend :: (w a -> b) -> w a -> w b
  duplicate :: w a -> w (w a)
~~~~

`extend` or `duplicate` are optional, as one can be written in terms of the
other one. The Monad typeclass, for reference, can be described as[^2] :

[^2]: In the real Haskell typeclass, there are the following differences: Monad
      and Functor are not related, `join` is a library function (you can't use
      it to define an instance), `(>>=)` is used instead of its flipped
      counterpart `(=<<)` and there two more methods `(>>)` and `fail`.

~~~~ {.haskell}
class Functor m => Monad m where
  return :: a -> m a
  (=<<) :: (a -> m b) -> m a -> m b
  join :: m (m a) -> m a
~~~~

The duality is quite easy to see : `extract` is the dual of `return`, `extend`
the one of `(=<<)` and `duplicate` the one of `join`.

So what are comonads good for ?

I stumbled upon [an article][sigfpe article] which explains that they can be
used for computations which depend on some local environment, like [cellular
automata]. Comments ask whether it's possible to generalize to higher
dimensions, which I will do by implementing [Conway's Game of Life] in a
comonadic way.

List Zippers
------------

List zippers are a fantastic data structure, allowing O(1) edits at a "cursor".
Moving the cursor element to element is O(1) too. This makes it a very nice data
structure when your edits are local (say, in a text editor). You can learn more
about zippers in general in this [post from Edward Z Yang]. The seminal paper is
of course [Huet's article].

A list zipper is composed of a cursor and two lists.

> data ListZipper a = LZ [a] a [a]

To go in a direction, you pick the head of a list, set it as your cursor, and
push the cursor on top of the other list. We assume that we will only infinte
lists, so this operation can not fail. This assumption is reasonnable especially
in the context of cellular automata[^3].

[^3]: Simulating a closed topology such as a torus may even be possible using
      cyclic lists instead of lazy infinite lists.
      **Update:** see Brian Cohen's response at the end of this post.

> listLeft :: ListZipper a -> ListZipper a
> listLeft (LZ (l:ls) x rs) = LZ ls l (x:rs)
> listLeft _ = error "listLeft"
>
> listRight :: ListZipper a -> ListZipper a
> listRight (LZ ls x (r:rs)) = LZ (x:ls) r rs
> listRight _ = error "listRight"

Reading and writing on a list zipper at the cursor is straightforward :

> listRead :: ListZipper a -> a
> listRead (LZ _ x _) = x
>
> listWrite :: a -> ListZipper a -> ListZipper a
> listWrite x (LZ ls _ rs) = LZ ls x rs

We can also define a function to convert a list zipper to a list, for example
for printing. As it's infinite on both sizes, it's not possible to convert it to
the whole list, so we have to pass a size parameter.

> toList :: ListZipper a -> Int -> [a]
> toList (LZ ls x rs) n =
>   reverse (take n ls) ++ [x] ++ take n rs

We can easily define a `Functor` instance for `ListZipper`. To apply a function
on whole zipper, we apply it to the cursor and map it on the two lists :

> instance Functor ListZipper where
>   fmap f (LZ ls x rs) = LZ (map f ls) (f x) (map f rs)

Time for the `Comonad` instance. The `extract` method returns an element from
the structure : we can pick the one at the cursor.

`duplicate` is a bit harder to grasp. From a list zipper, we have to build a
list zipper of list zippers. The signification behind this (confirmed by the
comonad laws that every instance has to fulfill) is that moving inside the
duplicated structure returns the original structure, altered by the same
move : for example, `listRead (listLeft (duplicate z)) == listLeft z`.

This means that at the cursor of the duplicated structure, there is the original
structure `z`. And the left list is composed of `listLeft z`, `listLeft
(listLeft z)`, `listLeft (listLeft (listLeft z))`, etc (same goes for the right
list).

The following function applies repeatedly two movement functions on each side of
the zipper (its type is more generic than needed for this specific case but
we'll instanciate `z` with something other than `ListZipper` in the next
section).

> genericMove :: (z a -> z a)
>             -> (z a -> z a)
>             -> z a
>             -> ListZipper (z a)
> genericMove a b z =
>   LZ (iterate' a z) z (iterate' b z)
>
> iterate' :: (a -> a) -> a -> [a]
> iterate' f = tail . iterate f

And finally we can implement the instance.

> instance Comonad ListZipper where
>   extract = listRead
>
>   duplicate = genericMove listLeft listRight

Using this comonad instance we can already implement 1D cellular automata, as
explained in the [sigfpe article]. Let's see how they can be extended to 2D
automata.

Plane zippers
-------------

Let's generalize list zippers to plane zippers, which are cursors on a plane
of cells. We will implement them using a list zipper of list zippers.

> data Z a = Z (ListZipper (ListZipper a))

We start by defining move functions. As a convention, the external list will
hold lines : to move up and down, we will really move left and right at the root
level.

> up :: Z a -> Z a
> up (Z z) = Z (listLeft z)
>
> down :: Z a -> Z a
> down (Z z) = Z (listRight z)

For left and right, it is necessary to alter every line, using the `Functor`
instance.

> left :: Z a -> Z a
> left (Z z) = Z (fmap listLeft z)
>
> right :: Z a -> Z a
> right (Z z) = Z (fmap listRight z)

Finally, editing is quite straightforward : reading is direct (first read the line,
then the cursor) ; and in order to write, it is necessary to fetch the current
line, write to it and write the new line.

> zRead :: Z a -> a
> zRead (Z z) = listRead $ listRead z
>
> zWrite :: a -> Z a -> Z a
> zWrite x (Z z) =
>   Z $ listWrite newLine z
>     where
>       newLine = listWrite x oldLine
>       oldLine = listRead z

Time for algebra. Let's define a `Functor` instance : applying a function
everywhere can be achieved by applying it on every line.

> instance Functor Z where
>   fmap f (Z z) = Z (fmap (fmap f) z)

The idea behind the `Comonad` instance for `Z` is the same that the `ListZipper`
one : moving "up" in the structure (really, "left" at the root level) returns
the original structure moved in this direction.

We will reuse the `genericMove` defined earlier in order to build list zippers
that describe movements in the two axes[^4].

[^4]: At first I thought that it was possible to only use the `Comonad` instance
      of `ListZipper` to define `horizontal` and `vertical`, but I couldn't come
      up with a solution. But in that case, the `z` generic parameter is
      instanciated to `Z`, not `ListZipper`. For that reason I believe that my
      initial thought can't be implemented. Maybe it's possible with a comonad
      transformer or something like that.

> horizontal :: Z a -> ListZipper (Z a)
> horizontal = genericMove left right
>
> vertical :: Z a -> ListZipper (Z a)
> vertical = genericMove up down

This is enough to define the instance.

> instance Comonad Z where
>   extract = zRead
>
>   duplicate z =
>     Z $ fmap horizontal $ vertical z

Conway's (comonadic) Game of Life
---------------------------------

Let's define a neighbourhood function. Here, directions are moves on a plane
zipper. Neighbours are : horizontal moves, vertical moves and their
compositions (`liftM2 (.)`)[^5].

[^5]: This could have been written in extension as there are only 8 cases, but
      it's funnier and arguably less error prone this way :-)

> neighbours :: [Z a -> Z a]
> neighbours =
>   horiz ++ vert ++ liftM2 (.) horiz vert
>     where
>       horiz = [left, right]
>       vert  = [up, down]
>
> aliveNeighbours :: Z Bool -> Int
> aliveNeighbours z =
>   card $ map (\ dir -> extract $ dir z) neighbours
>
> card :: [Bool] -> Int
> card = length . filter (==True)

The core rule of the game fits in the following function : if two neighbours are
alive, return the previous state ; if three neighbours are alive, a new cell is
born, and any other count causes the cell to die (of under-population or
overcrowding).

It is remarkable that its type is the dual of that of a Kleisli arrow (`a -> m b`).

> rule :: Z Bool -> Bool
> rule z =
>   case aliveNeighbours z of
>     2 -> extract z
>     3 -> True
>     _ -> False

And then the comonadic magic happens with the use of `extend` :

> evolve :: Z Bool -> Z Bool
> evolve = extend rule

`evolve` is our main transition function between world states, and yet it's only
defined in terms of the local transition function !

Let's define a small printer to see what's going on.

> dispLine :: ListZipper Bool -> String
> dispLine z =
>   map dispC $ toList z 6
>     where
>       dispC True  = '*'
>       dispC False = ' '
>
> disp :: Z Bool -> String
> disp (Z z) =
>   unlines $ map dispLine $ toList z 6

Here is the classic glider pattern to test. The definition has a lot of
boilerplate because we did not bother to create a `fromList` function.

> glider :: Z Bool
> glider =
>   Z $ LZ (repeat fz) fz rs
>     where
>       rs = [ line [f, t, f]
>            , line [f, f, t]
>            , line [t, t, t]
>            ] ++ repeat fz
>       t = True
>       f = False
>       fl = repeat f
>       fz = LZ fl f fl
>       line l =
>         LZ fl f (l ++ fl)

~~~~
*Main> putStr $ disp glider
             
             
             
             
             
             
             
        *    
         *   
       ***   
             
             
             
*Main> putStr $ disp $ evolve glider
             
             
             
             
             
             
             
             
       * *   
        **   
        *    
             
             
~~~~

We did it ! Implementing Conway's Game of Life is usually full of ad-hoc
boilerplate code : iterating loops, managing copies of cells, etc. Using the
comonadic structure of cellular automata, the code can be a lot simpler.

In this example, `ListZipper` and `Z` should be library functions, so the actual
implementation is only a dozen lines long!

The real benefit is that it has really helped be grasp the concept of comonads.
I hope that I did not just fall into the comonad tutorial fallacy :)

**Update (March 10th):** Brian Cohen contributed [a simple extension to simulate
a closed topology][BrianCohenLPaste]. Thanks !

[Literate Haskell]:          http://www.haskell.org/haskellwiki/Literate_programming
[source on github]:          https://github.com/emillon/blog.emillon.org
[Edward Kmett]:              http://comonad.com
[comonad package]:           http://hackage.haskell.org/package/comonad-3.0.0.2/docs/Control-Comonad.html
[category-extras package]:   http://hackage.haskell.org/package/category-extras-1.0.2
[sigfpe article]:            http://blog.sigfpe.com/2006/12/evaluating-cellular-automata-is.html
[post from Edward Z Yang]:   http://blog.ezyang.com/2010/04/you-could-have-invented-zippers/
[Huet's article]:            http://www.st.cs.uni-saarland.de/edu/seminare/2005/advanced-fp/docs/huet-zipper.pdf
[cellular automata]:         http://en.wikipedia.org/wiki/Cellular_automaton
[Conway's Game of Life]:     http://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
[BrianCohenLPaste]:          http://lpaste.net/83811
