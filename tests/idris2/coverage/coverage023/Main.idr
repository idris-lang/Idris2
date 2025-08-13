-- Declared in separate modules because, at the time of writing the test, type
-- constructors are compared by tags that are unique within a single module
import X
import Y

Uninhabited (X === Y) where
  uninhabited eq impossible
