import Data.So

myVoid : (0 _ : Void) -> ()
myVoid x = void x

foo : (y: Bool) -> (0 p : So y) => ()
foo False = myVoid (absurd p)
foo True  = ()

main : IO ()
main = pure (foo True)
