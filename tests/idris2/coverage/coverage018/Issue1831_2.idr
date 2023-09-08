module Issue1831_2

export
fooFromInteger : Num x => Integer -> x
fooFromInteger x = fromInteger (x + x)

%integerLit fooFromInteger

test : Nat
test = 5 + 6

test2 : Nat -> Bool
test2 1 = True
test2 _ = False
