private infixr 6 -*
(-*) : Type -> Type -> Type
(-*) a b = (1 _ : a) -> b

-- Test that the types of holes are not overly generalised wrt the
-- multiplicities in the function type

foo1 : (((1 _ : a) -> (1 _ : b) -> (1 _ : c) -> ()) -> ()) -> ()
foo1 f = f ?foo1h

foo2 : (((1 _ : a) -> (1 _ : b) -> (1 _ : c) -> ()) -> ()) -> ()
foo2 f = f (id ?foo2h)

foo3 : ((a -* b -* c -* ()) -> ()) -> ()
foo3 f = f (id ?foo3h)
