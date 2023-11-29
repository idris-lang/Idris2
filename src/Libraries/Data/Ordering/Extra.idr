module Libraries.Data.Ordering.Extra

%default total

infixl 5 `thenCmp`

export
thenCmp : Ordering -> Lazy Ordering -> Ordering
thenCmp LT _ = LT
thenCmp EQ o = o
thenCmp GT _ = GT
