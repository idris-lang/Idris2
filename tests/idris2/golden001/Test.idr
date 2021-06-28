module Test

import Test.Golden


tests : TestPool
tests
  = MkTestPool "Hello World"
               []
               Nothing
               [ "000-hello"]

export
main : IO ()
main = runner [ tests ]


-- [ EOF ]
