import Data.Vect

-- Check that `TTImp.ProcessDef.Dot` properly handles
-- functions in parameters and where clauses

parameters (str : String)
  0 foo : Vect n a -> Int
  foo [x, y, z] = 1
  foo _ = 2

bar : String -> ()
bar str = ()
  where
    -- We can't print case tree for nested function,
    -- so we just check that this function compiles
    0 baz : Vect n a -> Int
    baz [x, y, z] = 1
    baz _ = 2
