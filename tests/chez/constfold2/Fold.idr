import Data.Nat

%default total

record Small where
  constructor S
  value : Nat
  {auto 0 prf : LTE value 20}

Show Small where show = show . value

record Smaller where
  constructor XS
  value : Nat
  {auto 0 prf : LTE value 10}

-- This is the identity function
toSmall : Smaller -> Small
toSmall (XS v @{prf}) = S v @{transitive prf %search}

-- This is again the identity function
manyToSmall : List Smaller -> List Small
manyToSmall [] = []
manyToSmall (x::xs) = toSmall x :: manyToSmall xs

main : IO ()
main = printLn $ manyToSmall [XS 1, XS 2, XS 3]
