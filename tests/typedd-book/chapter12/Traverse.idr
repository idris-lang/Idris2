crew : List String
crew = ["Lister", "Rimmer", "Kryten", "Cat"]

main : IO ()
main = do putStr "Display Crew? "
          x <- getLine
          when (x == "yes") $
               do traverse putStrLn crew
                  pure ()
          putStrLn "Done"
