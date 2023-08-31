module Libraries.Data.WithDefault

export
data WithDefault : (0 a : Type) -> (0 def : a) -> Type where
  Default : WithDefault a def
  Value   : a -> WithDefault a def

export
value : a -> WithDefault a def
value = Value

export
defaultValue : WithDefault a def
defaultValue = Default

export
setDefault : a -> WithDefault a def -> WithDefault a def
setDefault v Default = Value v
setDefault _ v       = v

export
replaceDefault : WithDefault a def -> WithDefault a def'
replaceDefault Default = Default
replaceDefault (Value v) = Value v

export
collapseDefault : {def : a} ->
                  WithDefault a def -> a
collapseDefault Default = def
collapseDefault (Value v) = v

export
onWithDefault : (defHandler : Lazy b) ->
                (valHandler : a -> b) ->
                WithDefault a def ->
                b
onWithDefault defHandler _ Default = defHandler
onWithDefault _ valHandler (Value v) = valHandler v

export
collapseDefaults : Eq a =>
                   {def : a} ->
                   WithDefault a def ->
                   WithDefault a def ->
                   Either (a, a) a
collapseDefaults (Value x) (Value y) = if x /= y
                                       then Left (x, y)
                                       else Right x
collapseDefaults (Value x) Default   = Right x
collapseDefaults Default   (Value y) = Right y
collapseDefaults Default   Default   = Right def

export
isDefault : WithDefault a def -> Bool
isDefault Default = True
isDefault _ = False

export
isValue : WithDefault a def -> Bool
isValue Default = False
isValue (Value _) = True

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
  compare (Value x) (Value y) = compare x y
