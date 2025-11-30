data MyEq : a -> a -> Type where
  Impossible : Void => MyEq a b
  Refl       : MyEq a a

test : Not (MyEq Nat String)
test Impossible impossible

test2 : Not (MyEq Char String)
test2 Impossible impossible

test3 : Not (MyEq Type String)
test3 Impossible impossible

test4 : Not (MyEq Type Nat)
test4 Impossible impossible

test5 : Not (MyEq (List Nat) Type)
test5 Impossible impossible

test6 : Not (MyEq Bits64 Type)
test6 Impossible impossible

test7 : Not (MyEq 'a' 'b')
test7 Impossible impossible

-- The following ones are actually possible

test8 : Not (MyEq a Type)
test8 Impossible impossible

test9 : Not (MyEq a 'a')
test9 Impossible impossible

test10 : Not (MyEq a Nat)
test10 Impossible impossible

test11 : Not (MyEq 3 a)
test11 Impossible impossible
