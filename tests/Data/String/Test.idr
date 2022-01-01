module Data.String.Test

import Data.String

append_helper : (a : String) -> a = "" ++ a
append_helper = believe_me ()

unlines_is_distributive : (a, b : List String) -> unlines (a ++ b) = unlines a ++ unlines b
unlines_is_distributive [] [] = Refl
unlines_is_distributive [] a = append_helper (unlines a)
unlines_is_distributive (x::xs) b = cong ((x++"")++) (unlines_is_distributive xs b)

main : IO ()
main = do printLn ("<" ++ (unlines []) ++ ">")
          printLn ("<" ++ (unlines ["ab"]) ++ ">")
          printLn ("<" ++ (unlines ["a", "b"]) ++ ">")
          printLn ("<" ++ (fastUnlines []) ++ ">")
          printLn ("<" ++ (fastUnlines ["ab"]) ++ ">")
          printLn ("<" ++ (fastUnlines ["a", "b"]) ++ ">")
