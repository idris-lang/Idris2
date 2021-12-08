module Protocol.IDE.Holes

import Protocol.SExp

public export
record HolePremise where
  constructor MkHolePremise
  name : String -- Future: send more structured representation of:
                -- im/explicity (+ default value?) + quantity
  type : String -- Future: String + highlighting info

export
SExpable HolePremise where
  toSExp premise =
    SExpList [ StringAtom premise.name
             , StringAtom premise.type
             , SExpList [] -- TODO: metadata
             ]

public export
record HoleData where
  constructor MkHoleData
  name : String
  type : String -- Future : String + highlighting info
  context : List HolePremise

export
SExpable HoleData where
  toSExp hole = SExpList
    [ StringAtom (show  hole.name)
    , toSExp hole.context
    , SExpList [ toSExp hole.type   -- Conclusion
               , SExpList[]]        -- TODO: Highlighting information
    ]
