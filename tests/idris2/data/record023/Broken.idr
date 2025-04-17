module Broken

export
record VoidContainer where
  theVoid : Void

export
getVoid : (p : VoidContainer) -> Void
getVoid = theVoid
