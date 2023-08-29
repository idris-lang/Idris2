module Libraries.Data.WithDefault

public export
data WithDefault : (0 a : Type) -> (def : a) -> Type where
  Default : WithDefault a def
  Value   : a -> WithDefault a def

export
setDefault : a -> WithDefault a def -> WithDefault a def
setDefault k Default = Value k
setDefault _ v       = v

export
replaceDefault : WithDefault a def -> WithDefault a def'
replaceDefault Default = Default
replaceDefault (Value k) = Value k

export
collapseDefault : {def : a} ->
                  WithDefault a def -> a
collapseDefault Default = def
collapseDefault (Value a) = a

export
isDefault : WithDefault a def -> Bool
isDefault Default = True
isDefault _ = False

public export
Eq a => Eq (WithDefault a def) where
  Default == Default = True
  Default == Value _ = False
  Value _ == Default = False
  Value x == Value y = x == y

public export
Ord a => Ord (WithDefault a def) where
  compare Default   Default   = EQ
  compare Default   (Value _) = LT
  compare (Value _) Default   = GT
  compare (Value a) (Value b) = compare a b
