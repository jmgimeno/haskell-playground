> module MonadBehingZipper where

The Monads Hidden Behind Every Zipper

http://blog.sigfpe.com/2007/01/monads-hidden-behind-every-zipper.html

Uustalu points out that behind every zipper lies a comonad. I used this in my
cellular automaton example. What he doesn't mention is that there is also a
monad lurking behind every zipper and that it arises in a natural way. The
catch is that it's a monad in the wrong category making it tricky to express
in Haskell.

Firstly, what does "wrong category" mean? In the category of vector spaces,
every object is equipped with a commutative binary + operator. We can make no
such assumption in Haskell. What's more, Haskell doesn't easily allow us to
restrict type constructors to instances of Num say. So we can't easily
implement monads in the category of vector spaces as instances of Haskell's
Monad. Nonetheless, we can always write our own bind and return constrained
by Num, and that's what I'll do here. I believe there are workarounds that
don't involve GADT abuse but really I just want to illustrate an idea, not
write a complete working application.

As I've mentioned on #haskell, convolution is comonadic. A convolution (more
specifically, a discrete convolution) is a function that maps a (doubly
infinite) sequence of real numbers to another such sequence of real numbers in
such a way that each number in the new sequence is a weighted sum of numbers
in the old sequence and the weights depend only on the relative positions of
the numbers. For example: replacing each number in the sequence with the
average of it and its neighbours is a convolution.

Here's a simple example. Consider the sequence ...0,0,1,2,3,0,0,... We'll
replace each number with the sum of its neighbours and twice itself. So this
maps to ...,0,0+0+1,0+2*1+2,1+2*2+3,2+2*3+0,3+2*0+0,0,... The structure of
this computation is very similar to the structure of cellular automaton
evaluation and we can reuse that code here:


> data Zipper a = Zipper [a] [a] deriving (Eq,Show)

> left (Zipper (a:as) bs) = Zipper as (a:bs)
> right (Zipper as (b:bs)) = Zipper (b:as) bs

> class Comonad w where
>    coreturn :: w a -> a
>    cobind :: (w a -> b) -> w a -> w b

> iterate1 f x = tail $ iterate f x

> instance Comonad Zipper where
>    cobind f a = fmap f $ Zipper (iterate1 left a) (iterate right a)
>    coreturn (Zipper _ (b:_)) = b

> a = Zipper (repeat 0) ([0,1,2,3]++repeat 0)
> f (Zipper (a:_) (b:c:_)) = a+2*b+c

> test = let Zipper u v = cobind f a in take 5 v


When we run test we get [1,4,8,8,3].

Now think about the structure of this computation. We write a function f that
gathers up the value at a cell and its neighbours and computes the weighted
sum. cobind then applies this function all the way through our sequence to get
our result. The important thing is that f pulls in the data it needs,
distilling it down to one value, and that's why it has type Zipper a -> a.

There's another approach to convolution. We could push or scatter data. At each
point in the sequence we could take the value and push one copy left, one copy
right, and leave double the original value in place. Each cell will end up with
three values left in it and all we have to do is sum the values deposited in a
cell. What we want therefore is to take a value in a cell, of type a, and
generate an entire zipper full of values pushed from it, ie. a Zipper a. We'd
then like bind for the monad to sum over the returned zippers, staggering them
right and left as appropriate. Here's a table illustrating what I mean:

0 -> 0 0 0 0 0 0
1 -> 0 1 2 1 0 0
2 -> 0 0 2 4 2 0
3 -> 0 0 0 3 6 3
0 -> 0 0 0 0 0 0
----------------
     0 1 4 8 8 3

Unfortunately, as I pointed out above, bind for a monad can't perform
summations, so I have to define bind' and return' instead.

> plus (Zipper a b) (Zipper a' b') = Zipper (plus' a a') (plus' b b') where
>        plus' (a:as) (b:bs) = (a+b) : plus' as bs
>        plus' a [] = a
>        plus' [] a = a


Note that I'm going to assume that elements past the end of a list (so to speak)
actually represent zero and define new versions of left and right that produce
the required zeros on demand:

> left' (Zipper (a:as) bs) = Zipper as (a:bs)
> left' (Zipper [] bs) = Zipper [] (0:bs)
> right' (Zipper as (b:bs)) = Zipper (b:as) bs
> right' (Zipper as []) = Zipper (0:as) []

> tail' [] = []
> tail' a = tail a
> stagger f [] = []
> stagger f (x:xs) = x : map f (stagger f xs)
> stagger1 f x = tail' (stagger f x)

> instance Functor Zipper where
>    fmap f (Zipper a b) = Zipper (map f a) (map f b)

Here's our fake monad:

> return' a = Zipper [] [a]
> bind' f x = let Zipper a b = fmap f x
>            in foldl1 plus (stagger left' b ++ stagger1 right' a)

> a' = Zipper [] [0,1,2,3]
> f' x = Zipper [x] [2*x,x]

> test' = let Zipper u v = bind' f' a' in take 5 v


Run test' and we get the same result as before by a quite different method.

You should be able to see that in some sense comonads describe lazy
computations and monads represent strict ones. In strict languages you evaluate
your arguments first, and then push them into a function. In lazy languages you
call the function first, and it pulls in the value of its arguments as needed.
In fact, in Haskell we have a strictness monad and in ocaml you can implement a
lazy comonad. By and large, it's easier to write pull algorithms in Haskell.
Push algorithms are much easier to implement in a language with side effects.
In fact, one of the things that Haskell beginners need to learn is how to
rewrite push algorithms as pull algorithms and eliminate those side effects.

What I think is interesting here is that this dichotomy between push and pull,
scatter and gather, is pervasive all the way through computing, and it's quite
pretty that this deep notion it can be captured nicely by a(n almost) monad
and a comonad. Just to give an illustration of how pervasive it is consider 3D
rendering. We typically want to take a list of primitives and turn it into an
array of pixels. If we rasterise we push the primitives, asking for each
primitive, what pixels does it cover. If we ray-trace we pull on the pixels
asking, for each one, what primitives cover it. Many optimisations to both of
these approaches consist of making judicious decisions about which part of the
pipeline should be switched from push to pull or vice versa.

BTW I have an algorithm for automatically converting some types of pull
algorithm into push algorithms and vice versa. It's another one of those papers
that I keep meaning to finish and submit for publication one day...
