||| Test if the type of variables bound in as patterns is correctly reported
||| by :typeat, both in the pattern and in the right hand side

f : Maybe Nat -> Nat
f x@(Just y@(S _)) = ?rhs1 x y
f _ = ?rhs2
