||| Additional data types related to ordering notions
module Data.Order

%default total

||| Trichotomous formalises the fact that three relations are mutually exclusive.
||| It is meant to be used with relations that complement each other so that the
||| `Trichotomous lt eq gt` relation is the total relation.
public export
data Trichotomous : (lt, eq, gt : a -> a -> Type) -> (a -> a -> Type) where
  MkLT : {0 lt, eq, gt : a -> a -> Type} ->
         lt v w       -> Not (eq v w) -> Not (gt v w) -> Trichotomous lt eq gt v w
  MkEQ : {0 lt, eq, gt : a -> a -> Type} ->
         Not (lt v w) -> eq v w       -> Not (gt v w) -> Trichotomous lt eq gt v w
  MkGT : {0 lt, eq, gt : a -> a -> Type} ->
         Not (lt v w) -> Not (eq v w) -> gt v w       -> Trichotomous lt eq gt v w
