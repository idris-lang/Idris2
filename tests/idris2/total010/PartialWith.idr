%default total

partial
foo : Nat -> Nat
foo Z = Z

partial
bar : Nat -> Nat
bar n with (0)
 bar n | k = foo n
