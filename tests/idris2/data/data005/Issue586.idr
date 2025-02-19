mutual
  public export
  ListT : (m : Type -> Type) -> (a : Type) -> Type
  ListT m a = m (ListStruct m a)

  public export
  data ListStruct : (m : Type -> Type) -> (a : Type) -> Type where
    Nil  : ListStruct m a
    (::) : a -> ListT m a -> ListStruct m a
