data Three = A | B | C
data Bar : Type
data Foo : Type where
  MkFoo : Three -> Bar -> Foo

fun : Foo -> String
fun (MkFoo A y) = ""
fun (MkFoo B y) = ""

data Bar : Type where
  MkBar : Bar
