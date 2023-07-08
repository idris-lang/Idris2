import System.Term

main : IO ()
main = do
  width <- getTermCols
  height <- getTermLines
  printLn "Success \{show $ width > 0} \{show $ height > 0}"
