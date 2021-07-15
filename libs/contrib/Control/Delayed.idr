||| Utilities functions for conditionally delaying values.
module Control.Delayed

||| Type-level function for a conditionally infinite type.
public export
inf : Bool -> Type -> Type
inf False t = t
inf True t = Inf t

||| Type-level function for a conditionally lazy type.
public export
lazy : Bool -> Type -> Type
lazy False t = t
lazy True t = Lazy t
