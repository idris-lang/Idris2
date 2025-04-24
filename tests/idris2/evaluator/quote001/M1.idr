import M0

data Abs2 : List Unit' -> Type where
evalCheck : Abs2 f

evalAbs : (f : List Unit') -> (ext : List Unit') -> Abs2 (ext ++ f)
evalAbs f = \ ext => evalCheck {f = ext ++ f}
