-- Slides for the Continuation Tutorial
-- September 23, 2011 -- Toukyou, Japan.

module ContTutorial where

-- * Continuations are effects, and so we have to use monads
-- * The familiar Cont monad from the Monad transformer library
-- It is actually the monad of delimited control, as we shall see

import Control.Monad
import Control.Applicative

-- Let's see for simple expressions
-- Our earlier example in OCaml:
-- * reset (3 + shift (\k -> 5*2)) - 1

-- we have to use monads, and have to write the
-- expression in the monadic style

-- * The translation is mechanical
t1 = liftM2 (-)
     (reset 
      (liftM2 (+) (return 3)
        (shift (\k -> liftM2 (*) (return 5) (return 2)))))
     (return 1)

-- * it does look like scheme, doesn't it?
-- What is that return?
-- Lesson: the type can tell us a lot about the expression:
-- after all, a type is an approximation of the expression's
-- behavior, which tell us what an expression is without
-- running it. Can you guess what liftM2 does?
-- Now, what is the type of t1? What does it tell?

-- How to run:
t1r = runC t1
-- 9



-- * The expression t1 looks ugly, even to a Schemer.
-- We can write it better:

t1' = liftM2 (-)
     (reset 
      (liftM2 (+) (return 3)
        (shift (\k -> return (5*2)))))
     (return 1)

t1'r = runC t1'

-- * What did I do? How to justify what I just did?
-- An instance of the so-called monad law.

-- We can do more simplifications, this time syntactic
infixl 6 -!,+!
infixl 7 *!

(-!),(+!),(*!) :: (Num a, Monad m) => m a -> m a -> m a
(-!) = liftM2 (-)
(+!) = liftM2 (+)
(*!) = liftM2 (*)

t12 = reset (return 3 +! shift (\k -> return (5*2))) -! return 1

t12r = runC t12
-- 9

-- We can even remove return and so make the code look 
-- just like the OCaml code. Doing it is left as a homework.
-- We won't do that however.

-- * Explicitness in pursuit of insight is no vice.

-- More examples

-- * (3) fst (reset (fun () -> let x = [] in (x, x)))
-- We see that `let' corresponds to `do'
t13 = liftM fst (reset $ do
  x <- shift (\k -> return ("hi","bye"))
  return (x,x))

t13r = runC t13


-- (1) 5 * reset (fun () -> [] + 3 * 4)
-- (2) reset (fun () -> if [] then "hello" else "hi") ^ " world"
-- (3) fst (reset (fun () -> let x = [] in (x, x)))
-- (4) string_length (reset (fun () -> "x" ^ string_of_int []))

-- *//
-- * Rather than extracting a continuation as a function,
-- * and then applying to something, we apply it right away.

t2 = reset (return 3 +! shift (\k -> return (k (5*2)))) -! return 1
t2r = runC t2
-- 12

-- We can apply the captured continuation more than once within
-- the same expression:

t3 :: Cont Int Int
t3 = reset 
      (return 2 *! shift(\k -> return $ k (k 10))) +! return 1

t3r = runC t3
-- 41

-- * //
-- It is time now to introduce the continuation monad and
-- show how shift and reset are written in it.

newtype Cont w a = Cont{runCont :: (a -> w) -> w}

instance Monad (Cont w) where
  return x     = Cont (\k -> k x)
  Cont m >>= f = Cont (\k -> m (\v -> runCont (f v) k))

instance Functor (Cont w) where
    fmap f (Cont m) = Cont (\k -> m (k . f))

instance Applicative (Cont w) where
    pure    = return
    m <*> a = m >>= \h -> fmap h a

runC :: Cont w w -> w
runC m = runCont m id

reset :: Cont a a -> Cont w a
reset = return . runC

shift :: ((a -> w) -> Cont w w) -> Cont w a
shift f = Cont (runC . f)

-- * //

-- * The big question: is this correct? 
-- The results seem to be expected so far,
-- and in the agreement with OchaCaml. How to make sure they always
-- agree? To be certain, we need to say what is the specification
-- for shift/reset, and demonstrate that our implementation satisfies
-- the specification.

-- * Specification: so-called bubble-up semantics
-- which was the original semantics of delimited control (prompt/control)
-- introduced by Felleisen. That bubble-up semantics was re-discovered
-- for the so-called lambda-mu calculus, which is the calculus
-- for classical logic.

-- shift introduces a bubble
-- * shift body --> 泡 id body

-- The bubble propagates:
-- * (泡 k body) + e1 --> 泡 (\x -> (k x) + e1) body 
-- * (泡 k body) e1 --> 泡 (\x -> (k x) e1) body 
-- * f (泡 k body) -->  泡 (\x -> f (k x)) body 
-- * if (泡 k body) then e1 else e2 -->  
-- *     泡 (\x -> if (k x) then e1 else e2) body 

-- reset pricks (eliminates) the bubble
-- * reset (泡 k body) --> reset (body (\x -> reset (k x)))
-- * reset value --> value

-- The bubble-up semantics helps in practice, too: see
-- the end of this file.

-- * eta-expand shift 
-- to make the bubble representation explicit

shift' body = Cont (\k -> runC (body (\u -> runCont (return u) k)))

-- Here is the representation of the bubble:

泡 ctx body = Cont (\k -> runC (body (\u -> runCont (ctx u) k)))

-- * //
-- * Let us demonstrate that the propagation of the Cont bubble
-- * through the application matches the specification:
-- * (泡 k body) e1 --> 泡 (\x -> (k x) e1) body 

proof1 body ctx e =
 泡 ctx body <*> e
 ===
 泡 ctx body >>= \h -> (fmap h e)
 ===
 Cont (\ks -> runC (body (\u -> runCont (ctx u) ks))) >>=
   \h -> (fmap h e)
 ===
 Cont (\k ->
 (\ks -> runC (body (\u -> runCont (ctx u) ks)))
 (\v -> runCont ((\h -> (fmap h e)) v) k))
 ===
 Cont (\k ->
 (\ks -> runC (body (\u -> runCont (ctx u) ks)))
 (\v -> runCont (fmap v e) k))
 ===
 Cont (\k ->
 runC (body (\u -> runCont (ctx u) (\v -> runCont (fmap v e) k)))
 )
 -- an inner expression is almost the same as
 -- let g = (\v -> fmap v e) in
 -- ctx u >>= g ===
 --   Cont (\k1 -> runCont (ctx u) (\v -> runCont (g v) k1))
 -- modulo the replacement of k1 with k
 ===
 Cont (\k ->
 runC (body (\u -> runCont (ctx u >>= \v -> fmap v e) k)))
 ===
 let ctx' u = ctx u >>= \v -> fmap v e in
 Cont (\k -> runC (body (\u -> runCont (ctx' u) k)))
 ===
 let ctx' u = ctx u >>= \v -> fmap v e in
 泡 (\u -> ctx u >>= \v -> fmap v e) body
 ===
 泡 (\u -> ctx u <*> e) body

-- * To remind the specification rule:
-- * (泡 k body) e1 --> 泡 (\x -> (k x) e1) body 
-- * The result matches the specification.
-- * The other bubble-propagation rules can be checked
-- * similarly.

-- * //
-- Our equational proof was written in Haskell!
-- It was not mechanically checked. But at least it is well-typed.
-- GHC (at present) cannot verify that 
-- each step in the proof is valid; we need a real theorem prover for 
-- that. However GHC does verify that the premise is well-typed
-- and each step in the proof is type preserving.
-- GHC thus already catches many silly errors during equational
-- re-writing: mis-substitutions tend to break type preservation.

infixl 0 ===
-- `Propositional equality'
-- It should really be proven than `computed'. Therefore,
-- the computation below is trivial
(===) :: a -> a -> a
(===) = const

-- * Let us check that the Cont bubble elimination matches 
-- * the specification:
-- * reset (泡 ctx body) --> reset (body (\x -> reset (ctx x)))

proof2 body ctx =
 reset (泡 ctx body) 
 ===
 reset (Cont (\k -> runC (body (\u -> runCont (ctx u) k))))
 ===
 return (runC (Cont (\k -> runC (body (\u -> runCont (ctx u) k)))))
 ===
 return ((\k -> runC (body (\u -> runCont (ctx u) k))) id)
 ===
 return (runC (body (\u -> runCont (ctx u) id)))
 ===
 reset (body (\u -> runCont (ctx u) id))
 ===
 reset (body (\u -> runC (ctx u)))

-- * If the k were of the type a -> Cont w a, we would have
-- * added return, and noticed that return . runC === reset
-- The continuation captured by shift is a pure
-- function (that is, has no effects), we make this
-- fact explicit in its type.

-- We now demonstrate that the Cont monad reset when applied
-- to a value returns the value:
-- * reset value --> value

proof3 v =
 reset (return v)
 ===
 reset (Cont (\k -> k v))
 ===
 return (runC (Cont (\k -> k v)))
 ===
 return ((\k -> k v) id)
 ===
 return v

-- If determining the result of t3 in your head was difficult,
-- let us show how the bubble-up semantics helps.
-- The bubble-up semantics makes determining the result of t3
-- a pure mechanical operation.
t3r' = 
 runC (reset 
       (return 2 *! shift(\k -> return $ k (k 10))) +! return 1)
 -- shift introduces the bubble
 ===
 runC (reset 
       (return 2 *! 泡 return (\k -> return $ k (k 10))) +! return 1)
 -- the bubble propagates up and devours `return 2 *!'
 ===
  runC (reset 
      (泡 (\x -> return 2 *! return x) 
           (\k -> return $ k (k 10))) +! return 1)
 -- simplifying using the monad law
 ===
  runC (reset 
      (泡 (\x -> return (2 * x))
           (\k -> return $ k (k 10))) +! return 1)
 -- reset pricks the bubble
 ===
  runC (reset ((\k -> return $ k (k 10)) (\x -> runC (return (2 * x)))) 
        +! return 1)
 -- runC . return === id
 ===
  runC (reset ((\k -> return $ k (k 10)) (\x -> 2 * x)) +! return 1)
 -- beta-reduction
 ===
  runC (reset (return 40) +! return 1)
 -- reset of a value
 ===
  runC (return 40 +! return 1)
 -- monad law (addition of pure expressions)
 ===
  runC (return 41)
 ===
 41



 