import Debug.Trace

calc : Nat -> Nat
calc n0 =
  let n1  = delay $ (trace "foo" $ n0 + n0)
      n2  = delay $ (trace "bar" $ 2 * n1)
      n3  = delay $ (trace "baz" $ 2 * n2)
   in if n0 > 10 then n2 else n3

main : IO ()
main = do printLn (calc 100)

