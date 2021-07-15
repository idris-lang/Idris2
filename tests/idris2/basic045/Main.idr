
foo : Semigroup a => a -> ()
foo x = ()

main : IO ()
main = pure (foo ())
