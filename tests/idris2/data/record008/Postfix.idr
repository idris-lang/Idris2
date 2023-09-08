module Postfix

record Diag (a : Type) where
  fstt   : a
  sndd   : a
  equal : fstt === sndd

val : Diag a -> a
val diag = diag .fstt

prf : (d : Diag a) -> val d === d.sndd
prf = ?a

(.val') : Diag a -> a
diag .val' = diag .sndd

sym : (d : Diag a) -> d .fstt === d .val'
sym = ?b
