import Language.JSON

import Data.List
import Data.String

main : IO ()
main = printLn $ filter (not . roundTrips) chars
  where chars : List Int
        chars = [0 .. 55295]

        roundTrips : Int -> Bool
        roundTrips n =
          let s = singleton $ chr n
              v = JString s
           in case parse (show v) of
                   Just (JString x) => x == s
                   _                => False

