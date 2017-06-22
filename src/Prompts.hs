module Prompts where

import Control.Monad ((>=>))
import Data.Maybe (maybe)
import System.IO (hFlush, stdout)
import Text.Read (readMaybe)

prompt :: String -> IO String
prompt msg = putStr (msg ++ ": ") >> hFlush stdout >> getLine

withCond :: (a -> Maybe b) -> (b -> Bool) -> (a -> Maybe b)
find `withCond` p  = find >=> (\b -> if (p b) then Just b else Nothing)

firstOne :: Monad m => (a -> Maybe b) -> [m a] -> m b
firstOne find (ma:mas) = do a <- ma
                            maybe (firstOne find mas) return (find a)

ensuring :: IO a -> (a -> Maybe b) -> IO b
ensuring prompt find = firstOne find $ repeat $ prompt

main = do a <- prompt "enter a" `ensuring` (readMaybe `withCond` (>0))
          b <- prompt "enter b" `ensuring` (readMaybe `withCond` (>0))
          print $ a + b
