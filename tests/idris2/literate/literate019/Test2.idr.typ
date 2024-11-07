/* idris
module Test2
*/

= Another test, with extended extension

/* idris
silentlyDeclaredFunction' : Nat -> Nat
silentlyDeclaredFunction' = (+6)
*/

Some text here

== How, some visible code

```idris
f' : Nat -> Nat
f' = (+8) . silentlyDeclaredFunction'
```

/* idris
g' : Nat -> Nat
g' = silentlyDeclaredFunction' . f'
*/

And now a hidden failing block:

/* idris
failing "ff"
  h : Nat -> Nat
  h = ff + 1
*/
