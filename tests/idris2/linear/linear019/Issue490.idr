data MyList : Type -> Type where
  Nil : {a : Type} -> MyList a
  (::) : {a : Type} -> a -> MyList a -> MyList a

g : MyList a -> ()
g [] = ()
g l@(x :: xs) = ?hole
