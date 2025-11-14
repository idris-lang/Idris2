data Identity : Type -> Type where
  MkIdentity : (a : Type) -> a -> Identity a

foo : Identity Bool -> ()
foo (MkIdentity .(Bool) True)  = ()
foo (MkIdentity .(Bool) False) = ()
