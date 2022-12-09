data Tuple : Type -> Type where
  MkTuple : {0 a : Type} -> a -> a -> Tuple a

ohno : Void
ohno = (case True of
  True => MkTuple Unit
  False => MkTuple Unit) Unit
