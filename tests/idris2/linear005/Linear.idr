module Linear

public export
data Usage = Once | Many

public export
data Use : Usage -> (Type -> Type) -> Type -> Type where
     Pure : (1 x : a) -> Use t m a
     BindOnce : (1 act : Use Once m a) -> (1 k : (1 x : a) -> Use t m b) -> Use t m b
     BindMany : (1 act : Use Many m a) -> (1 k : (x : a) -> Use t m b) -> Use t m b

public export
contType : (Type -> Type) -> Usage -> Usage -> Type -> Type -> Type
contType m Once q a b = ((1 x : a) -> Use q m b)
contType m Many q a b = ((x : a) -> Use q m b)

public export
(>>=) : {p : _} -> (1 f : Use p m a) -> (1 k : contType m p q a b) -> Use q m b
(>>=) {p = Once} = BindOnce
(>>=) {p = Many} = BindMany

public export
pure : (1 x : a) -> Use t m a
pure = Pure

public export
One : (Type -> Type) -> Type -> Type
One = Use Once

public export
Any : (Type -> Type) -> Type -> Type
Any = Use Many

infix 2 @@

public export
data Res : (a : Type) -> (a -> Type) -> Type where
     (@@) : (x : a) -> (1 res : r x) -> Res a r
