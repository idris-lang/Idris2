data Foo : Nat -> Type where

0 G : (0 yv : Nat) -> Type
G yv = Foo yv -> Bool

partial
f : (0 x : Nat) -> Nat
f x = case G x of
           (Foo x' -> _) => x'
