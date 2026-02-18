main : IO ()
main = do
  putStrLn $ show res
  where zzz : Int
        zzz = 2
        add : Int -> Int
        add zzz = zzz + zzz
        res : Int
        res = add 1
