
data Natural : Type where
    S : Natural -> Natural
    Z : Natural

%builtin Natural Natural

plus : Natural -> Natural -> Natural
plus Z y = y
plus (S x) y = S (plus x y)

main : IO Natural
main = pure $ plus (S Z) (S $ S Z)
