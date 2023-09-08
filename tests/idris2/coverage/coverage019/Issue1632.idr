%default total

data Command : Type -> Type where
    Empty : Command ()
    Pure : t -> Command t

test : Command (List a) -> ()
test (Pure x) = ()

test2 : Command (a -> b) -> ()
test2 (Pure x) = ()

test3 : Command Type -> ()
test3 (Pure x) = ()
