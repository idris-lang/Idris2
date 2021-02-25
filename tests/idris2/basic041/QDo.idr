namespace MyDo
  export
  (>>=) : a -> (a -> IO b) -> IO b
  (>>=) val k = k val

  export
  (>>) : a -> IO b -> IO b
  a >> f = a >>= const f

foo : IO ()
foo = MyDo.do
         x <- "Silly"
         putStrLn x

namespace A
  namespace B
    export
    (>>=) : Nat -> (() -> Nat) -> Nat
    (>>=) x fy = x + (fy ())

    export
    (>>) : Nat -> Nat -> Nat
    a >> f = a >>= const f

test : Nat
test = B.A.do
         5
         _ <- 6
         7

test2 : Nat
test2 = A.B.do
         5
         _ <- 6
         7
