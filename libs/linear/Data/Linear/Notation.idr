module Data.Linear.Notation

%default total

export infixr 0 -@
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

export prefix 5 !*
||| Prefix notation for the linear unrestricted modality
public export
data (!*) : Type -> Type where
  MkBang : a -> !* a

||| Unpack an unrestricted value in a linear context
public export
unrestricted : !* a -@ a
unrestricted (MkBang unr) = unr

||| Unpack an unrestricted value in a linear context
|||
||| A postfix alias for function unrestricted.
public export
(.unrestricted) : !* a -@ a
(.unrestricted) = unrestricted
