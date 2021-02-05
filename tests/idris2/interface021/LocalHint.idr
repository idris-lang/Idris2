Gnu : Type
Gnu = Int

Foo : Type
Foo = Bool

A : Foo
A = True

mkFoo : Gnu -> Foo
mkFoo gnu = A

gnat : {auto startHere : (a : Foo ** a = A)} -> Unit
gnat = ()

%logging 0
pathology : (gnu : Gnu) -> Unit
pathology gnu =
  let %hint foo : Foo
      foo = mkFoo gnu
      %hint bar : Foo -> (ford : arg = A)
                      -> (a : Foo ** a = A)
      bar _ Refl = (A ** Refl)
  in gnat
%logging 0
