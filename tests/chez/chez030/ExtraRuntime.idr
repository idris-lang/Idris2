%foreign "scheme:my-mul"
myMul : Int -> Int -> Int

main : IO ()
main = do
  putStrLn $ "6 * 7 = " ++ show (myMul 6 7)
