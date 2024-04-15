-- see https://github.com/idris-lang/Idris2/issues/2995

%default total

%tcinline
zs : Stream Nat
zs = Z :: zs

%tcinline
zs' : Stream Nat -> Stream Nat
zs' xs = Z :: zs' xs

%tcinline
zs'' : Stream Nat -> Stream Nat
zs'' = \xs => Z :: zs'' xs