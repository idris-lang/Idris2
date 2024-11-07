= A test of literate Idris for typst

/* idris
silentlyDeclaredFunction : Nat -> Nat
silentlyDeclaredFunction = (+6)
*/

Some text here

== How, some visible code

```idris
f : Nat -> Nat
f = (+8) . silentlyDeclaredFunction
```
