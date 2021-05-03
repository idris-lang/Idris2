%default total

test : (String, ()) -> ()
test ("a", ()) = ()

test' : (Int, ()) -> ()
test' (1, ()) = ()

test'' : Type -> Type
test'' (List a) = a
