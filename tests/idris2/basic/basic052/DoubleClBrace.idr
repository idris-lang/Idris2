module DoubleClBrace

f : {a : Nat} -> Nat
f {a} = a + 1

g : {b : Nat} -> Nat
g {b} = b + 2

h : Nat -> Nat
h c = g {b = f {a=c}}
