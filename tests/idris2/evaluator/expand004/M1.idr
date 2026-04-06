module M1

import M0

export
Name : Type
Name = String

export
FromString Name where
  fromString = id

export
STRING : DecEq String
STRING = %search

export
DecEq Name where
  decEq = decEq @{STRING}
