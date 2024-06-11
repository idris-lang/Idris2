module Futures

import System.Future

-- Checks the interference between CSE optimisations and de-optimisations
-- and management of lazy values

topLevelConstant : Lazy String
topLevelConstant = "top-level indeed"

main : IO ()
main = do
  let a = await $ fork topLevelConstant
  putStrLn a
