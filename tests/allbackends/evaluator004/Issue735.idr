interface Natty (n : Nat) where

fromNatty : Type -> Nat
fromNatty (Natty Z) = Z
fromNatty (Natty (S n)) = S (fromNatty (Natty n))
fromNatty _ = Z

main : IO ()
main = ignore $ traverse printLn
  [ fromNatty (Natty 3)
  , fromNatty (Natty (2 + 6))
  , fromNatty (List (Natty 1))
  ]
