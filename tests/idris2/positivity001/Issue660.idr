module Issue660

%default total

data Sig : (a : Type) -> (a -> Type) -> Type where

data Value : Unit -> Type where
  MkV : Sig Unit Value -> Value ()
