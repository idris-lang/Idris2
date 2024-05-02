%default total

%tcinline_fuel 42

%tcinline
f : Nat -> a -> a
f Z x = x
f (S k) x = f k x

-- this will typecheck
g1 : Nat -> Nat
g1 Z = Z
g1 (S k) = g1 (f 41 k)

-- but this will not
g2 : Nat -> Nat
g2 Z = Z
g2 (S k) = g2 (f 42 k)