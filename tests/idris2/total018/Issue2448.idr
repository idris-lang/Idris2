-- https://github.com/idris-lang/Idris2/issues/2448#issuecomment-1117103496

%default total

boom : Nat -> Void
boom (S x) = boom x
boom x = boom x
