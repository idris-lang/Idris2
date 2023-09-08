module FuncImpl

public export
interface Monad m => FooBar m where
  Foo    : {A : Type} -> A -> m A -> Type
  bar    : {A : Type} -> (ma : m A) -> m (DPair A (\ a => Foo a ma))
  foobar : {A : Type} -> (ma : m A) -> map DPair.fst (bar ma) = ma
