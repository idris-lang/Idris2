module Data.Linear.Notation

%default total

infixr 0 -@
||| Infix notation for linear implication
public export
(-@) : Type -> Type -> Type
a -@ b = (1 _ : a) -> b

||| Linear identity function
public export
id : a -@ a
id x = x

||| Linear function composition
public export
(.) : (b -@ c) -@ (a -@ b) -@ (a -@ c)
(.) f g v = f (g v)

prefix 5 !*
||| Prefix notation for the linear unrestricted modality
public export
record (!*) (a : Type) where
  constructor MkBang
  unrestricted : a
