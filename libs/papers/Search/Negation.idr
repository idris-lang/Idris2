module Search.Negation

import Data.List.Quantifiers
import Data.Nat

%default total

||| It is much easier to look for positive evidence than it is to look
||| for negative evidence. So instead of looking for `Not q`, we may
||| want to look for `p` instead
public export
interface Negates p q | q where
  toNegation : p -> Not q

public export
({0 x : a} -> Negates (p x) (q x)) => Negates (All p xs) (Any q xs) where
  toNegation all = allNegAny (mapProperty toNegation all)

public export
({0 x : a} -> Negates (p x) (q x)) => Negates (Any p xs) (All q xs) where
  toNegation any = anyNegAll (mapProperty toNegation any)

public export
Negates (m `LT` n) (m `GTE` n) where
  toNegation = LTImpliesNotGTE

public export
Negates (m `LTE` n) (m `GT` n) where
  toNegation = LTEImpliesNotGT
