test : Builtin.Equal S (\x : a => S ?)
test = Refl

test2 : ?
test2 = {a : _} -> the (S = \x : a => S _) Refl
