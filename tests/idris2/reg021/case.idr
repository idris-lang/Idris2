twice : Char -> Char -> Char -> Char -> Nat -> (Nat, Nat)
twice w x y z Z = (Z, Z)
twice m n o p (S x)
    = case twice m n o p x of
           (a, b) => (S a, S b)

bothS : Int -> String -> (Nat, Nat) -> (Nat, Nat)
bothS test dummy = \(c, d) => (S c, S d)

pf : (x : Nat) -> twice 'a' 'b' 'c' 'd' (S x)
                     = bothS 99 "red balloons" (twice 'a' 'b' 'c' 'd' x)
pf k = Refl -- Refl
