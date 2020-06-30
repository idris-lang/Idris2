import Text.Readline

testComplete : String -> Int -> IO (Maybe String)
testComplete text 0 = pure $ Just "hamster"
testComplete text 1 = pure $ Just "bar"
testComplete text st = pure Nothing

loop : IO ()
loop = do Just x <- readline "> "
               | Nothing => putStrLn "EOF"
          putStrLn x
          when (x /= "") $ addHistory x
          if x /= "quit"
             then loop
             else putStrLn "Done"

main : IO ()
main = do setCompletionFn testComplete
          loop
