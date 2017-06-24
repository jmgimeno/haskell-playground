module Prompts where

import Control.Monad ((>=>))
import Data.Maybe (maybe)
import System.IO (hFlush, stdout)
import Text.Read (readMaybe)

prompt :: String -> IO String
prompt msg = putStr (msg ++ ": ") >> hFlush stdout >> getLine

withCond :: (a -> Maybe b) -> (b -> Bool) -> (a -> Maybe b)
extract `withCond` cond = extract >=> (\b -> if (cond b) then Just b else Nothing)

guarantee :: Monad m => (a -> Maybe b) -> [m a] -> m b
guarantee extract (ma:mas) = do a <- ma
                                maybe (guarantee extract mas) return (extract a)

ensuring :: Monad m => m a -> (a -> Maybe b) -> m b
ensuring prompt extract = guarantee extract $ repeat $ prompt

main = do a <- prompt "enter a" `ensuring` (readMaybe `withCond` (>0))
          b <- prompt "enter b" `ensuring` (readMaybe `withCond` (>0))
          print $ a + b
