namespace MyDo
  export
  (>>=) : a -> (a -> IO b) -> IO b
  (>>=) val k = k val

foo : IO ()
foo = MyDo.do
         x <- "Silly"
         putStrLn x
