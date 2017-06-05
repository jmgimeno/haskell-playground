import Tex (display)
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  file <- readFile $ head args
  mapM_ (putStrLn . display) $ map read $ lines file
