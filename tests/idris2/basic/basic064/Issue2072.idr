data Elem : Type -> List Type -> Type where

Types : (0 a : Type) -> Eq a => List Type

export
body :  (0 _ : Eq t1)
     => {auto 0 _ : Elem Bool (Types t1)}
     -> (obj : t1)
     -> (obj == obj) === maybe True (const False) (guard (obj == obj))
