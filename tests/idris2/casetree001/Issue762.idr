import Data.Singleton

%default total

-- data constructors
f : Singleton (MkPair True) -> Bool
f (Val _) = True

-- type constructors
g : Singleton Maybe -> Bool
g (Val _) = True
