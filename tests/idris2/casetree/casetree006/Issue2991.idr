0
foo : (0 a : Type) -> a -> a
foo Int x = x + 10
foo _ x = x

0
test : foo Nat (the Nat 7) = (the Nat 7)
test = Refl
