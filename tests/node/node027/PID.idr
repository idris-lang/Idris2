import System

assert : Bool -> IO ()
assert b = if b
  then pure ()
  else assert_total $ idris_crash ""

main : IO ()
main = do
  assert $ !getPID /= 0
