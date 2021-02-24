test : Not (Nat = String)
test Refl impossible

test2 : Not (Char = String)
test2 Refl impossible

test3 : Not (Type = String)
test3 Refl impossible

test4 : Not (Type = Nat)
test4 Refl impossible

test5 : Not (List Nat = Type)
test5 Refl impossible

test6 : Not (Bits64 = Type)
test6 Refl impossible

test7 : Not ('a' = 'b')
test7 Refl impossible

-- The following ones are actually possible

test8 : Not (a = Type)
test8 Refl impossible

test9 : Not (a = 'a')
test9 Refl impossible

test10 : Not (a = Nat)
test10 Refl impossible

test11 : Not (3 = a)
test11 Refl impossible
