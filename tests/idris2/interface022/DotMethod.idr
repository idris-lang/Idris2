data D = MkD
data E = MkE

interface I i where
 (.idot) : i -> Int

I D where
 (.idot) _ = 0

interface J i where
 (.jdot) : i -> Int
 (.jdot) _ = 0

J D where
J E where
  (.jdot) _ = 1
