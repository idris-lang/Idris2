f : { a, b : Type } -> Either a b -> Either b a
f {a=b} x = x
f (Right x) = Left x
f (Left x) = Right x
