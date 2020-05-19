data Foo : Type -> Type where
     IsNat : Foo Nat
     IsBool : Foo Bool

okay : a -> Foo a -> Bool
okay Z IsNat = False
okay True IsBool = True

bad : a -> Foo a -> Bool
bad Z IsNat = False
bad True IsBool = True
bad (Just 0) _ = False
