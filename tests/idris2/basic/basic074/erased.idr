data X : Type -> Type where
  A : X ()
  B : X Void

f : (0 _ : X ()) -> ()
f A = ()

g : (0 _ : X Void) -> ()
g B = ()
