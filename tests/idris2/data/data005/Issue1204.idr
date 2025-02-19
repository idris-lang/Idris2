data Tm = Foo Nat

mutual
  Env : Type
  Env = List Clos

  data Clos : Type where
    Cl : Tm -> Env -> Clos
