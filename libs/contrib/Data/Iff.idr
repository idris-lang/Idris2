module Data.Iff

import Decidable.Order

||| Predicate for when one type is inhabited
||| if an only if the other type is
public export
record Iff a b where
  constructor MkIff
  implies : a -> b
  impliedBy : b -> a

public export
Preorder Type Iff where
  transitive a b c ab bc = MkIff
    (\x => implies bc $ implies ab x )
    (\x => impliedBy ab $ impliedBy bc x)
  reflexive a = MkIff id id

public export
Equivalence Type Iff where
  symmetric a b (MkIff aToB bToA) = MkIff bToA aToB
