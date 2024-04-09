-- see https://github.com/idris-lang/Idris2/issues/2995

%default total

-- %tcinline -- uncomment this, your compiler will hang forever
-- terminate after adding fuel
zs : Stream Nat
zs = Z :: zs

-- %tcinline -- uncomment this, your compiler will hang forever
-- terminate after adding fuel
zs' : Stream Nat -> Stream Nat
zs' xs = Z :: zs' xs

-- %tcinline -- uncomment this, your compiler will hang forever
-- terminate after adding fuel
zs'' : Stream Nat -> Stream Nat
zs'' = \xs => Z :: zs'' xs