module Data.Singleton

||| The type containing only a particular value.
||| This is useful for calculating type-level information at runtime.
public export
data Singleton : a -> Type where
     Val : (x : a) -> Singleton x

-- pure and <*> implementations for idiom bracket notation

public export
pure : (x : a) -> Singleton x
pure = Val

public export
(<*>) : Singleton f -> Singleton x -> Singleton (f x)
Val f <*> Val x = Val (f x)
