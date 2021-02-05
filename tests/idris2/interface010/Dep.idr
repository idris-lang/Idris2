module Dep

interface Monad m => FooBar m where
  Foo : {0 a : Type} -> a -> m a -> Type
  Bar : {0 A : Type} -> m A -> Type
  foo : {0 A : Type} -> (x : A) -> (ma : m A) -> Foo x ma -> Bar ma
