
module NoRegression

import Data.Vect

data Dep : (n : Nat) -> (a : Type) -> Vect n a -> Type where
   MkDep : Dep n a v

dpairParse : (   n : Nat
              ** a : Type
              ** v : Vect n a
              ** Dep n a v
             )
dpairParse = (_ ** _ ** ["a", "b"] ** MkDep)
