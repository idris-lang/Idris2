%default total

test : (f : () -> Bool) -> f () = True
test (\x => True) = Refl

bad : False = True
bad = test (\() => False)
