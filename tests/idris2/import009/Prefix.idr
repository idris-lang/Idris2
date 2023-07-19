module Prefix

private
prefix 5 !!

export
(!!) : Type -> Type
(!!) = Not

export
test : Either (!! a) (!! b) -> !! (a, b)
test f (x, y) = f (Left x)
