module Prompts where

import Control.Monad ()
import Data.Maybe
import System.IO
import Text.Read (readMaybe)


rePrompt :: IO a -> (a -> Maybe b) -> (b -> Bool) -> IO b
rePrompt prompt find cond
  = do a <- prompt
       case find a of
         Nothing -> doRePrompt
         Just b -> if (cond b)
                   then return b
                   else doRePrompt
    where doRePrompt = putStrLn "Re-enter value" >> rePrompt prompt find cond

main = do a <- rePrompt (prompt "enter a") readMaybe (>0)
          b <- rePrompt (prompt "enter b") readMaybe (>0)
          print $ a + b

-----------------------------------------------------------------------------
fusion :: (a -> Maybe b) -> (b -> Bool) -> (a -> Maybe b)
fusion f g = f >=> (\b -> if (g b) then Just b else Nothing)

rePrompt' :: IO a -> (a -> Maybe b) -> IO b
rePrompt' prompt find
  = do a <- prompt
       case find a of
         Nothing -> putStrLn "Re-enter value" >> rePrompt' prompt find
         Just b -> return b

main' = do a <- rePrompt' (prompt "enter a") $ fusion readMaybe (>0)
           b <- rePrompt' (prompt "enter b") $ fusion readMaybe (>0)
           print $ a + b

------------------------------------------------------------------------------
prompt :: String -> IO String
prompt msg = putStr (msg ++ ": ") >> hFlush stdout >> getLine

withCond :: (a -> Maybe b) -> (b -> Bool) -> (a -> Maybe b)
find `withCond` p  = find >=> (\b -> if (p b) then Just b else Nothing)

firstOne :: Monad m => (a -> Maybe b) -> [m a] -> m b
firstOne find (ma:mas) = do a <- ma
                            maybe (firstOne find mas) return (find a)

rePrompt'' :: IO a -> (a -> Maybe b) -> IO b
rePrompt'' prompt find = firstOne find $ repeat $ prompt

main'' = do a <- rePrompt'' (prompt "enter a") $ readMaybe `withCond` (>0)
            b <- rePrompt'' (prompt "enter b") $ readMaybe `withCond` (>0)
            print $ a + b
