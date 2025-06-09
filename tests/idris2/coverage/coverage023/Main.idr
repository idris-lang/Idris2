module Main

-- Declared in separate modules because, at the time of writing the test, type
-- constructors are compared by tags that are unique within a single module
import X
import Y

Uninhabited (X === Y) where
  uninhabited eq impossible

data X = MkX

Uninhabited (X.X === Main.X) where
  uninhabited eq impossible
