From Bits to Cells: Simple Cellular Automata in Haskell, Part Two

http://praisecurseandrecurse.blogspot.com.es/2006/12/from-bits-to-cells-simple-cellular_19.html


> module FromBitsToCellsPt2 where

Last time we defined a function to generate the next state of a given
cell in our cellular universe, given a rule number and a tuple consisting
of the current state of the cell to the left, the cell itself, and the
cell to the right.

> import Data.Bits

> genNextBit :: Int -> ( Bool, Bool, Bool ) -> Bool
> genNextBit rulenum ( left, center, right ) = rulenum `testBit` idx
>    where idx = ( if left then (4::Int) else (0::Int) ) .|.
>           ( if center then (2::Int) else (0::Int) ) .|.
>           ( if right then (1::Int) else (0::Int) )

Recall that we can use automatic currying to make a rule-applying
function like so:

> rule_30 = genNextBit 30

We can ask GHCi for the type:

:type rule_30

rule_30 :: (Bool, Bool, Bool) -> Bool

I've put it off while I work on the rules, but it is time to figure out
how to actually represent our CA universe. Let's start by using a list.
I know that I'm going to write a number of inefficient functions, and
do evil things like take the length of lists a lot, but let's suspend all
concerns about efficiency over to a future discussion and consider this
purely a proof-of-concept.

Our inital universe at time zero has one cell set to True:

> initial_universe = [True]

But that isn't quite the right representation for the universe, because
it implies that our whole universe is one cell in size. We can't even
apply our rule once because there is no left cell and right cell!
Really, we want to pretend that we have an _infinite_ universe; at
time zero, all the cells to the left and right hold False. Remember,
Haskell is so powerful that it can traverse an infinite list in only
0.0003 seconds! Well, if you don't evaluate the whole thing, that is.
Taking advantage of lazy evaluation, you can define all kinds of
infinite structures. This construct will give us an infinite list of
False values:

> allFalse :: [Bool]
> allFalse = False : allFalse

We don't want to evaluate allFalse, but we can partially evaluate it
using a function like take. So can we represent our universe like this?

> genInfiniteUniverse :: [Bool] -> [Bool]
> genInfiniteUniverse known_universe = allFalse ++ known_universe ++ allFalse

Let's try it:

take 10 ( genInfiniteUniverse initial_universe )

[False,False,False,False,False,False,False,False,False,False]

Nope! Since the left-hand side of the universe is infinite, we will
never reach the middle element, no matter how far we travel from the
start of the list!

That's no good. However, we can do it another way. We'll allow our
universe to be expanded on demand on the left and right sides:

> expandUniverse :: Int -> [Bool] -> [Bool]
> expandUniverse expand_by known_universe =
>   ( take expand_by allFalse ) ++ known_universe ++ ( take expand_by allFalse )

expandUniverse 3 initial_universe

[False,False,False,True,False,False,False]

We can use the expandUniverse function to expand our initial universe
out to a standardized width before we start applying the rules.

First, here's a routine to stringify a universe for display:

> boolToChar :: Bool -> Char
> boolToChar True = '#'
> boolToChar False = ' '

> stringifyUniverse :: [Bool] -> String
> stringifyUniverse ls = map boolToChar ls

Now our infrastructure is in place, so let's figure out how to apply
our generator rule. We know that we want to start with our initial
universe. Let's expand it to a fixed size. This will give us enough
elements to start making left/center/right tuples out of each consecutive
set of three cells. Each tuple is then used to look up the next state
of the cell at the center; this will become an element in our next
universe. Then we move to the next cell (not three cells down). This
means that the tuples overlap.

Let's make the tuples. We have to do some thinking here and consider
all the cases; the behavior isn't immediately obvious. The following
almost works:

universeToTuples :: [Bool] -> [(Bool, Bool, Bool)]
universeToTuples universe | length universe >= 3 =
   ( universe !! 0, universe !! 1, universe !! 2 ) :
   universeToTuples ( tail universe )
universeToTuples universe = []

universeToTuples [False, True, True, True, False]

[(False,True,True),
(True,True,True),
(True,True,False)]

But it isn't quite right; it leaves off the end cases; when we apply
our rules, the intermediate representation of the universe as a list
of tuples to look up cell mappings will shrink. We actually want the
following tuples:

[(False,False,True),
(False,True,True),
(True,True,True),
(True,True,False),
(True,False,False)]

where the first element of the list is considered as if it was just
to the right of an implied False, and the last element is considered
as if it was just to the left of another implied False. This sounds
like another place we can use our universe expander:

> universeToTuples :: [Bool] -> [(Bool, Bool, Bool)]
> universeToTuples [] = []
> universeToTuples universe = tupleize $ expandUniverse 1 universe
>   where
>       tupleize xs =
>            if length xs > 3 then tuple3 xs : tupleize ( tail xs )
>               else [ tuple3 xs ]
>       tuple3 xs = ( xs !! 0, xs !! 1, xs !! 2 )

Why did I write it that way? Well, I tried to write tupleize using
guards, special-casing length xs > 3 followed by an unguarded case for
all other possibilities, but GHC didn't like it -- it told me I had
non-exhaustive patterns. There is probably a smarter way to write this,
but note that we definitely don't want this version:

universeToTuples universe = ( xs !! 0, xs !! 1, xs !! 2 )
    : universeToTuples ( tail xs )
       where xs = expandUniverse 1 universe

In that version, the universe keeps expanding as we walk down the list,
and we never get to the end!

OK, now that we have our tuples, we want to turn them into our new
universe, given a cellular rule number:

> tuplesToUniverse :: Int -> [(Bool, Bool, Bool)] -> [Bool]
> tuplesToUniverse rule [] = []
> tuplesToUniverse rule (tup:tups) = genNextBit rule tup : tuplesToUniverse rule tups

Note that we don't have to explicitly take the tail since we provide a
name for it in the pattern. We're ready to define our genUniverses function
that applies a given CA rule. We can express a given generation like this:

> nextUniverse :: Int -> [Bool] -> [Bool]
> nextUniverse rule universe = tuplesToUniverse rule $ universeToTuples universe

Now, let's generalize it:

> genUniverses :: Int -> Int -> Int -> [[Bool]]
> genUniverses rule width count = take count
>    ( iterate ( nextUniverse rule ) ( expandUniverse ( width `div` 2 ) initial_universe ) )

(You could also use a fold, and I'm sure there are lots of other ways to
do it, but iterate seems to work fine).

And now, witness the unfolding of a universe! Note that the parameters
that go to genUniverses are the rule number, the width for display, and the
number of generations:

putStr $ unlines $ map stringifyUniverse $ genUniverses 222 19 10

($ removes green)

          #
         ###
        #####
       #######
      #########
     ###########
    #############
   ###############
  #################
 ###################

In general, a width of twice the number of generations - 1 will show
all the transitions we are interested in; you could consider the diagonal
area above to be the "light cone" of events causally connected to that
single point (although some rules will generate True cells outside of
that "light cone" based on the other False values in the initial universe).
Let's make a helper function to choose a width for us:


> showRule rule gens =
>   putStr $ unlines $ map stringifyUniverse $
>       genUniverses rule ( gens * 2 - 1 ) gens

Let's try a few of the other rules:

showRule 252 15
              #
              ##
              ###
              ####
              #####
              ######
              #######
              ########
              #########
              ##########
              ###########
              ############
              #############
              ##############
              ###############

showRule 78 15
               #
              ##
             ###
            ## #
           ### #
          ## # #
         ### # #
        ## # # #
       ### # # #
      ## # # # #
     ### # # # #
    ## # # # # #
   ### # # # # #
  ## # # # # # #
 ### # # # # # #

And finally, my all-time favorite, which simulates a Sierpinski gasket:

showRule 82 32
                                #
                               # #
                              #   #
                             # # # #
                            #       #
                           # #     # #
                          #   #   #   #
                         # # # # # # # #
                        #               #
                       # #             # #
                      #   #           #   #
                     # # # #         # # # #
                    #       #       #       #
                   # #     # #     # #     # #
                  #   #   #   #   #   #   #   #
                 # # # # # # # # # # # # # # # #
                #                               #
               # #                             # #
              #   #                           #   #
             # # # #                         # # # #
            #       #                       #       #
           # #     # #                     # #     # #
          #   #   #   #                   #   #   #   #
         # # # # # # # #                 # # # # # # # #
        #               #               #               #
       # #             # #             # #             # #
      #   #           #   #           #   #           #   #
     # # # #         # # # #         # # # #         # # # #
    #       #       #       #       #       #       #       #
   # #     # #     # #     # #     # #     # #     # #     # #
  #   #   #   #   #   #   #   #   #   #   #   #   #   #   #   #
 # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

Wow!
Followup: I had mentioned that my code had a bug, because some pictures, such
as this one:

showRule 29 11
          #
  ######### ###########
  #         #
  ######### ###########
  #         #
  ######### ###########
  #         #
  ######### ###########
  #         #
  ######### ###########
  #         #
look different than the way Wolfram's book and web site shows them, which is
like this:

            #
  ######### ###########
            #
  ######### ###########
            #
  ######### ###########
            #
  ######### ###########
            #
  ######### ###########
            #
After a little investigation this seems to be because Wolfram's implementation
wraps around; the left neighbor of the leftmost cell of a given universe is
taken from the rightmost cell, and vice-versa, while my implementation pretends
that there is always more empty space available to the left and right.

Whether you consider this a bug or not is up to you. The wraparound behavior is
probably considered more "canonical." You can compare the results from my
program to the pictures at Wolfram's MathWorld site here. If you replace my
universeToTuples function with this one:

universeToTuples :: [Bool] -> [(Bool, Bool, Bool)]
universeToTuples [] = []
universeToTuples universe = tupleize $ wrapUniverse universe
   where
       wrapUniverse xs =  ( last xs ) : ( xs ++ [ head xs ] )
       tupleize xs =
           if length xs > 3 then tuple3 xs : tupleize ( tail xs )
               else [ tuple3 xs ]
       tuple3 xs = ( xs !! 0, xs !! 1, xs !! 2 )

you will get the wraparound behavior.
