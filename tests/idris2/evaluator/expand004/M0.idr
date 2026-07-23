module M0

public export
interface DecEq t where
  decEq : (x1 : t) -> (x2 : t) -> Dec (x1 = x2)

public export
[FromEq] Eq a => DecEq a where
    decEq x y = case x == y of
                     True => Yes primitiveEq
                     False => No primitiveNotEq
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

public export
DecEq String where
    decEq = decEq @{FromEq}

