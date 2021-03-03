%default total

data Singleton : {a : Type} -> a -> Type where
  Val : (x : a) -> Singleton x

-- data constructors
f : Singleton (MkPair True) -> Bool
f (Val _) = True

-- type constructors
g : Singleton Maybe -> Bool
g (Val _) = True
