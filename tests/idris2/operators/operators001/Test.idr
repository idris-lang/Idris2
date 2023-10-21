

autobind infixr 0 =@

0 (=@) : (a : Type) -> (a -> Type) -> Type
(=@) a f = (1 x : a) -> f x


data S : {ty : Type} -> (x : ty) -> Type where
  MkS : (x : ty) =@ S x
  -- same as
  -- MkS : (1 x : ty) -> S x


