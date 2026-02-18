%logging "declare.def.lhs" 10


data Tup : (a,b : Type) -> Type where
  MkTup : (1 f : a) -> (1 s : b) -> Tup a b

f : Tup a b -> a
f (MkTup f s) = f
