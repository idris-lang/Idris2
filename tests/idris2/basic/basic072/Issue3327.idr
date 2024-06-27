foo : IO Nat

test1 : IO ()
test1 = do
  x : Nat <- foo
  printLn x

test2 : IO ()
test2 = do
  1 x : Nat <- foo
  printLn x

test3 : IO ()
test3 = do
  0 x : Nat <- foo
  printLn x

test4 : IO ()
test4 = do
  1 x <- foo
  printLn x

test5 : IO ()
test5 = do
  0 x <- foo
  printLn x

bar : IO (Maybe Nat)

test6 : IO ()
test6 = do
  Just x : Maybe Nat <- bar
    | Nothing => pure ()
  printLn x


