import Data.Vect

data VectN : Type -> Type where
     MkVectN : (n : Nat) -> Vect n a -> VectN a

doSearch : Nat -> VectN Int
doSearch n = MkVectN ?vlength [1,2,3,4]
