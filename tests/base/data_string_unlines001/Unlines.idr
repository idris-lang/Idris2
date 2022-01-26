import Data.String

main : IO ()
main = do printLn ("<" ++ (unlines []) ++ ">")
          printLn ("<" ++ (unlines ["ab"]) ++ ">")
          printLn ("<" ++ (unlines ["a", "b"]) ++ ">")
          printLn ("<" ++ (fastUnlines []) ++ ">")
          printLn ("<" ++ (fastUnlines ["ab"]) ++ ">")
          printLn ("<" ++ (fastUnlines ["a", "b"]) ++ ">")
