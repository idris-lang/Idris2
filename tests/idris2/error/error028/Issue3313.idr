data Expr : Type -> Type where
    Add : (Integral n) => n -> n -> Expr n

eval : (Integral n) => Expr n -> n
eval (Add x y) = x + y
