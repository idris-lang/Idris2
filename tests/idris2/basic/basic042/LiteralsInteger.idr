import Data.Fin

%default total

data ZeroOneOmega = Zero | One | Omega

Num ZeroOneOmega where
  Zero + a = a
  a + Zero = a
  One + a = Omega
  a + One = Omega
  Omega + Omega = Omega

  Zero * _ = Zero
  _ * Zero = Zero
  One * a = a
  a * One = a
  Omega * Omega = Omega

  fromInteger 0 = Zero
  fromInteger 1 = One
  fromInteger _ = Omega

test1 : ZeroOneOmega
test1 = 0

test2 : ZeroOneOmega
test2 = 1

test3 : ZeroOneOmega
test3 = 8
