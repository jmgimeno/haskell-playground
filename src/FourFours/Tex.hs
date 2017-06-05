module Tex (display) where

import Tree

tex :: Tree -> String
tex p@(Plus a b)                = binop "+" p a b
tex p@(Minus a b)               = binop "-" p a b
tex p@(Expt a b)                = binop "^" p a b
tex p@(Times a b)               = binop "\\times" p a b
tex p@(Divide a@(Divide x y) b) = frac (divide a x y) (group p b)
tex p@(Divide a b)              = frac (group p a) (group p b)
tex p@(Negate a)                = prefix "-" p a
tex p@(Factorial a)             = postfix "!" p a
tex (Sqrt a)                    = "\\sqrt{" ++ tex a ++ "}"
tex Four                        = "4"

binop :: String -> Tree -> Tree -> Tree -> String
binop op p a b = group p a ++ " " ++ op ++ " " ++ group p b

prefix :: String -> Tree -> Tree -> String
prefix op p a = "{" ++ op ++ group p a ++ "}"

postfix :: String -> Tree -> Tree -> String
postfix op p a = "{" ++ group p a ++ op ++ "}"

divide :: Tree -> Tree -> Tree -> String
divide a x y = (group a x ++ " / " ++ group a y)

frac :: String -> String -> String
frac num denom = "\\frac{" ++ num ++ "}{" ++ denom ++ "}"

group :: Tree -> Tree -> String
group parent child
  | p > c     = "(" ++ t ++ ")"
  | p == c    = "{" ++ t ++ "}"
  | otherwise = t
  where
    p = precedence parent
    c = precedence child
    t = tex child

precedence :: Tree -> Integer
precedence (Plus _ _)    = 1
precedence (Minus _ _)   = 1
precedence (Times _ _)   = 2
precedence (Divide _ _)  = 2
precedence (Negate _)    = 3
precedence (Sqrt _)      = 3
precedence (Factorial _) = 3
precedence (Expt _ _)    = 3
precedence Four          = 5

display :: (Integer, Tree) -> String
display (n, t) = show n ++ " = " ++ tex t
