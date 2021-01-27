data Foo : Type where [noHints]
  A : Foo
  B : Foo

findA : {auto foo : Foo} -> String
findA {foo = A} = "Found an A"
findA {foo = _} = "Failed to find an A"

Baz : String -> Type
Baz s = s = "Found an A"

baz : (s : String ** Baz s)
baz = let %hint arg : Foo
          arg = A
      in (findA ** Refl)

interface Gnu where
  constructor MkGnu
  hasFoo : Foo

findB : Gnu => String
findB = case hasFoo of
  B => "Found a B"
  _ => "Failed to find a B"

Bar : String -> Type
Bar s = s = "Found a B"

bar : (s : String ** Bar s)
bar = let %hint arg : Gnu
          arg = MkGnu B
      in (findB ** Refl)

interface Gnat a where
  constructor MkGnat
  makeFoo : a -> Foo

record More where
  constructor MkMore
  0 Ty : Type

%unbound_implicits off
bug : forall a . a -> (s : String ** Bar s)
bug {a} x = let M : More
                M = MkMore a
                %hint arg : Gnat (Ty M)
                arg = MkGnat (const B)
            in (findB ** Refl)
