module Data.So

import Data.Bool

%default total

||| Ensure that some run-time Boolean test has been performed.
|||
||| This lifts a Boolean predicate to the type level. See the function `choose`
||| if you need to perform a Boolean test and convince the type checker of this
||| fact.
|||
||| If you find yourself using `So` for something other than primitive types,
||| it may be appropriate to define a type of evidence for the property that you
||| care about instead.
public export
data So : Bool -> Type where
  Oh : So True

export
Uninhabited (So False) where
  uninhabited Oh impossible

||| Perform a case analysis on a Boolean, providing clients with a `So` proof
export
choose : (b : Bool) -> Either (So b) (So (not b))
choose True  = Left Oh
choose False = Right Oh

export
decSo : (b : Bool) -> Dec (So b)
decSo True  = Yes Oh
decSo False = No uninhabited

export
eqToSo : b = True -> So b
eqToSo Refl = Oh

export
soToEq : So b -> b = True
soToEq Oh = Refl

||| If `b` is True, `not b` can't be True
export
soToNotSoNot : So b -> Not (So (not b))
soToNotSoNot Oh = uninhabited

||| If `not b` is True, `b` can't be True
export
soNotToNotSo : So (not b) -> Not (So b)
soNotToNotSo = flip soToNotSoNot

export
soAnd : {a : Bool} -> So (a && b) -> (So a, So b)
soAnd soab with (choose a)
  soAnd {a=True}  soab | Left Oh = (Oh, soab)
  soAnd {a=True}  soab | Right prf = absurd prf
  soAnd {a=False} soab | Right prf = absurd soab

export
andSo : (So a, So b) -> So (a && b)
andSo (Oh, Oh) = Oh

export
soOr : {a : Bool} -> So (a || b) -> Either (So a) (So b)
soOr soab with (choose a)
  soOr {a=True}  _    | Left Oh = Left Oh
  soOr {a=False} soab | Right Oh = Right soab

export
orSo : Either (So a) (So b) -> So (a || b)
orSo (Left Oh)  = Oh
orSo (Right Oh) = rewrite orTrueTrue a in
                  Oh
