module Issue735

-- Not allowed to pattern-match on under-applied constructors
isCons : (a -> List a -> List a) -> Bool
isCons (::) = True
isCons _ = False

interface A a where

-- Not allowed to pattern-match on under-applied type constructors
test : (kind : Type -> Type) -> Maybe Nat
test A = Just 1
test _ = Nothing
