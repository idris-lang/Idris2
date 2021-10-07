record Nat2 where
  nat : Nat

f : Nat2 -> Nat2
f = { nat $= floor }
