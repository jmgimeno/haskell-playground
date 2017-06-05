import Tree
import Data.Maybe (mapMaybe)
import Data.Set (difference, elems, fromList, Set)

solutions :: Set Int
solutions = fromList $ mapMaybe evalToInt $ trees $ replicate 4 Four

main :: IO ()
main = print $ elems $ difference (fromList [0..20]) solutions
