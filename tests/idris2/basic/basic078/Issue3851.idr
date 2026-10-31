namespace Unit
  export f : () -> ()

namespace Bool
  export f : Bool -> Bool

g : (forall m . Monad m => Nat -> ()) -> ()

-- verify implicit lambdas are inserted
test : ()
test = f . g $ \x => ?res

