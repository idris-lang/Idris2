parameters (n : Nat)
    data X : Type -> Type where
         A : t -> X t
         B : t -> X t

    Eq t => Eq (X t) where
      A x == A y = x == y
      B x == B y = x == y
      _ == _ = False

    test : Char -> Char -> Bool
    test x y = A x == A y

mkEq : (approx : Bool) -> Eq Nat
mkEq True = withinOne
  where
    [withinOne] Eq Nat where
      Z == Z = True
      Z == S Z = True
      S Z == Z = True
      S x == S y = x == y
      _ == _ = False
mkEq False = %search
