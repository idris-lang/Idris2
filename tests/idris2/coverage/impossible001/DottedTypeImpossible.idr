data Identity : Type -> Type where
  MkIdentity : (a : Type) -> a -> Identity a

foo : Identity Bool -> Void -> ()
foo (MkIdentity .(Bool) True)  _ impossible
foo (MkIdentity .(Bool) False) _ impossible
