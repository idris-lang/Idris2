module Issue1831_1

export
fooFromInteger : Num x => Integer -> x
fooFromInteger x = fromInteger (x + x)

%integerLit Issue1831_1.fooFromInteger

test : Nat
test = 5 + 6

test2 : Nat -> Bool
test2 1 = True
test2 _ = False
