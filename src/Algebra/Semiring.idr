module Algebra.Semiring

%default total

export infixl 8 |+|
export infixl 9 |*|

||| A Semiring has two binary operations and an identity for each
public export
interface Semiring a where
  (|+|) : a -> a -> a
  plusNeutral : a
  (|*|) : a -> a -> a
  timesNeutral : a

||| Erased linearity corresponds to the neutral for |+|
public export
erased : Semiring a => a
erased = plusNeutral

||| Purely linear corresponds to the neutral for |*|
public export
linear : Semiring a => a
linear = timesNeutral

||| A semiring eliminator
public export
elimSemi : (Semiring a, Eq a) => (zero : b) -> (one : b) -> (a -> b) -> a -> b
elimSemi zero one other r {a} =
  if r == Semiring.plusNeutral {a}
     then zero
     else if r == Semiring.timesNeutral {a}
             then one
             else other r

export
isErased : (Semiring a, Eq a) => a -> Bool
isErased = elimSemi True False (const False)

export
isLinear : (Semiring a, Eq a) => a -> Bool
isLinear = elimSemi False True (const False)

export
isRigOther : (Semiring a, Eq a) => a -> Bool
isRigOther = elimSemi False False (const True)

export
branchZero : (Semiring a, Eq a) => Lazy b -> Lazy b -> a -> b
branchZero yes no rig = if isErased rig then yes else no

export
branchOne : (Semiring a, Eq a) => Lazy b -> Lazy b -> a -> b
branchOne yes no rig = if isLinear rig then yes else no

export
branchVal : (Semiring a, Eq a) => Lazy b -> Lazy b -> a -> b
branchVal yes no rig = if isRigOther rig then yes else no

export
presence : Semiring a => Eq a => a -> a
presence = elimSemi erased linear (const linear)
