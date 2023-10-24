%default total

test : (f : () -> Bool) -> f === (\x => True) -> f () = True
test (\x => True) Refl = Refl
