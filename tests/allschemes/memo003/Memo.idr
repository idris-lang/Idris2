-- This tests checks, whether lazy values constants are
-- properly memoized. If they are not, this test
-- will perform 10^20 additions and will therefore not
-- finish in reasonable time.

-- Turn on weak memoisation
%cg chez lazy=weakMemo
%cg racket lazy=weakMemo

-- We return lazy values in a monad to avoid behaviour of common expression elimination

nx : Lazy Nat -> IO $ Lazy Nat
nx n = pure $ delay $ force n + force n + force n + force n + force n + force n + force n + force n + force n + force n

main : IO ()
main = do
  n0 <- pure 1
  n1 <- nx n0
  n2 <- nx n1
  n3 <- nx n2
  n4 <- nx n3
  n5 <- nx n4
  n6 <- nx n5
  n7 <- nx n6
  n8 <- nx n7
  n9 <- nx n8
  n10 <- nx n9
  n11 <- nx n10
  n12 <- nx n11
  n13 <- nx n12
  n14 <- nx n13
  n15 <- nx n14
  n16 <- nx n15
  n17 <- nx n16
  n18 <- nx n17
  n19 <- nx n18
  n20 <- nx n19
  printLn n20
