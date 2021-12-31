module Data.String.Test

import Data.String.Extra

unlines : List String -> String
unlines = join "\n"

empty_string_equal : "" = ""
empty_string_equal = Refl

empty_list_equal : Prelude.Nil = Prelude.Nil
empty_list_equal = Refl

unlines_empty_list_helper : unlines [] = ""
unlines_empty_list_helper = Refl

unlines_is_distributive : (a, b : List String) -> unlines (a ++ b) = unlines a ++ unlines b 
unlines_is_distributive [] [] = unlines_empty_list_helper
unlines_is_distributive a b = Refl

main : IO ()
main = do printLn ("<" ++ (unlines []) ++ ">")
          printLn ("<" ++ (unlines ["ab"]) ++ ">")
          printLn ("<" ++ (unlines ["a", "b"]) ++ ">")
          printLn ("<" ++ (fastUnlines []) ++ ">")
          printLn ("<" ++ (fastUnlines ["ab"]) ++ ">")
          printLn ("<" ++ (fastUnlines ["a", "b"]) ++ ">")
