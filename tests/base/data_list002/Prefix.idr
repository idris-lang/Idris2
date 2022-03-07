import Data.List
import Data.String

byLength : Nat -> String -> Maybe (String, Nat)
byLength n str = (str, n) <$ guard (String.length str == n)

bySuccess : a -> (a -> Maybe b) -> Maybe b
bySuccess = flip ($)

-- cheating to display the remaining (const Nothing) function in 3rd case
Show b => Show (List a -> b) where
  show f = "\\ _ => " ++ show (f [])

main : IO ()
main = putStr $ unlines
  [ show $ prefixOfBy byLength [5,5,1] ["hello", "world", "!", "Not", "seen"]
  , show $ suffixOfBy byLength [3,4] ["hello", "world", "!", "Not", "seen"]
  , show $ prefixOfBy bySuccess [[1],[1,2],[]] [head', head' <=< tail', const (pure 3), const Nothing]
  ]
