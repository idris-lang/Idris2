record Wrap (a : ?hole) where
  constructor MkWrap
  proj : a

record Unit (a : ?hole2) where
  constructor MkUnit

record Tree (a : ?hole3) where
  isThree : 3 === a
