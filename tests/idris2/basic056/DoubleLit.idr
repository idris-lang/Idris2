import Data.So

record Newtype where
  constructor
  MkNewtype
  wrapped : Double

FromDouble Newtype where
  fromDouble = MkNewtype

Show Newtype where
  showPrec p (MkNewtype v) = showCon p "MkNewtype" $ showArg v


record InUnit where
  constructor MkInUnit
  value      : Double
  0 inBounds : So (0 <= value && value <= 1)

Show InUnit where
  showPrec p (MkInUnit v _) = showCon p "MkInUnit" $ showArg v ++ " _"

namespace InUnit
  public export
  fromDouble :  (v : Double)
             -> {auto 0 prf : So (0 <= v && v <= 1)}
             -> InUnit
  fromDouble v = MkInUnit v prf


main : IO ()
main = do printLn $ the InUnit 0.25
          printLn $ the Newtype 123.456
