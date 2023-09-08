interface Queue (0 q: Type -> Type) where
  empty : q a
  isEmpty : q a -> Bool
  snoc : q a -> a -> q a
  head : q a -> a
  tail : q a -> q a

data CatList : (Type -> Type) -> Type -> Type where
  E : CatList q a
  C : {0 q : Type -> Type} -> a -> q (Lazy (CatList q a)) -> CatList q a

link : (Queue q) => CatList q a -> Lazy (CatList q a) -> CatList q a
link E s = s -- Just to satisfy totality for now.
link (C x xs) s = C x (snoc xs s)
