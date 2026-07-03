-- See https://github.com/idris-lang/Idris2/pull/1899
-- A smaller variant of the test to check that no inlining happen for Force/Delay

n0 : Lazy Nat
n0 = S Z

n1 : Lazy Nat
n1 = n0 + n0
