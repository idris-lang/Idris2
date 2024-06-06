module Data.Singleton

||| The type containing only a particular value.
||| This is useful for calculating type-level information at runtime.
public export
data Singleton : a -> Type where
     Val : (x : a) -> Singleton x

public export %inline
reindex : (0 _ : x === y) -> Singleton x -> Singleton y
reindex Refl x = x

public export %inline
unVal : Singleton {a} x -> a
unVal $ Val x = x

public export %inline
(.unVal) : Singleton {a} x -> a
(.unVal) = unVal

-- pure and <*> implementations for idiom bracket notation

public export
pure : (x : a) -> Singleton x
pure = Val

public export
(<*>) : Singleton f -> Singleton x -> Singleton (f x)
Val f <*> Val x = Val (f x)
