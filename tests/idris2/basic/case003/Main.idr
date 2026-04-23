data X : Type -> Type where
  MkX : (a : Type) -> X a

partial
foo : (t : Type) -> X ((a : t) -> Type) -> ()
foo t (MkX (t -> Type)) = ()
