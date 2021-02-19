module Main

%default total

%logging "declare.data.parameters" 20
%logging "eval.eta" 10


-- explicit
data Value : (value : Nat -> Type) -> Type where
  EmptyV : {0 value : Nat -> Type} -> Value (\ n => value n)

data TValue : Nat -> Type where
  MkTupleV : Value (\n => TValue n) -> TValue n
