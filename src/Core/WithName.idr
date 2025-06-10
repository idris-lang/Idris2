module Core.WithName

import Core.FC
import Core.Name

-------------------------------------------------------------------------------
-- With Name functor to carry name information with a payload

public export
record WithName (ty : Type) where
  constructor MkWithName
  name : WithFC Name
  val : ty

export
mapWName : (ty -> sy) -> WithName ty -> WithName sy
mapWName f = {val $= f}

