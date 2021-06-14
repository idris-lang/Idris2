%default total

nice : (x : Bool) -> x === True
nice .(_) = Refl
