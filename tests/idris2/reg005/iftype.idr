data Elem	 : 	a -> List a -> Type where
    Here	 : 	Elem x (x :: xs)
    There	 : 	(later : Elem x xs) -> Elem x (y :: xs)


data TypeWithFunction : Type where
    ABC  : (ty_a:Type) -> (ty_b:Type) -> (ty_a -> ty_b) -> TypeWithFunction

isInList : Elem (ABC Bool String (\c => if c then "Foo" else "Bar"))
                [(ABC Bool String (\c => if c then "Foo" else "Bar"))]
isInList = Here

isInListBad : Elem (ABC Bool String (\c => if c then "Foo" else "Bar"))
                  [(ABC Bool String (\c => if c then "Foo" else "Baz"))]
isInListBad = Here
