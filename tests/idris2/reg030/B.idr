module B

public export
record Rec where
  constructor MkRec
  field : Char --- Unit and Bool don't cause the bug

public export
defaultRec : Rec
defaultRec = MkRec 'a'
