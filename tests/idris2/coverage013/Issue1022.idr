test : Not (Nat = String)
test eq impossible

test2 : Not (Char = String)
test2 eq impossible

test3 : Not (Type = String)
test3 eq impossible

test4 : Not (Type = Nat)
test4 eq impossible

test5 : Not (List Nat = Type)
test5 eq impossible

test6 : Not (Bits64 = Type)
test6 eq impossible

test7 : Not ('a' = 'b')
test7 eq impossible

-- The following ones are actually possible

test8 : Not (a = Type)
test8 eq impossible

test9 : Not (a = 'a')
test9 eq impossible

test10 : Not (a = Nat)
test10 eq impossible

test11 : Not (3 = a)
test11 eq impossible
