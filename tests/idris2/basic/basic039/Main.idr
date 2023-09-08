module Main

-- Using :di we can see the internal structure. MkFoo should be a newtype,
-- MkBar not
data Foo : Type where
  MkFoo : String -> Foo

data Bar : Type where
  [noNewtype]
  MkBar : String -> Bar
