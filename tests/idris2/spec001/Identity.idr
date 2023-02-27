%logging "compiler.identity" 5

%spec a
identity : List a -> List a
identity [] = []
identity (x :: xs) = x :: identity xs

test : List Nat -> List Nat
test ns = identity ns
