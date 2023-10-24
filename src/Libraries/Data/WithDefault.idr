module Libraries.Data.WithDefault

export
data WithDefault : (0 a : Type) -> (0 def : a) -> Type where
  DefaultedValue : WithDefault a def
  SpecifiedValue : a -> WithDefault a def

export
specified : a -> WithDefault a def
specified = SpecifiedValue

export
defaulted : WithDefault a def
defaulted = DefaultedValue

export
specifyValue : a -> WithDefault a def -> WithDefault a def
specifyValue v DefaultedValue = SpecifiedValue v
specifyValue _ v              = v

export
replaceSpecified : WithDefault a def -> WithDefault a def'
replaceSpecified DefaultedValue     = DefaultedValue
replaceSpecified (SpecifiedValue v) = SpecifiedValue v

export
collapseDefault : {def : a} -> WithDefault a def -> a
collapseDefault DefaultedValue     = def
collapseDefault (SpecifiedValue v) = v

export
onWithDefault : (defHandler : Lazy b) ->
                (valHandler : a -> b) ->
                WithDefault a def ->
                b
onWithDefault defHandler _ DefaultedValue     = defHandler
onWithDefault _ valHandler (SpecifiedValue v) = valHandler v

export
collapseDefaults : Eq a =>
                   {def : a} ->
                   WithDefault a def ->
                   WithDefault a def ->
                   Either (a, a) a
collapseDefaults (SpecifiedValue x) (SpecifiedValue y) = if x /= y
                                                         then Left (x, y)
                                                         else Right x
collapseDefaults (SpecifiedValue x) DefaultedValue   = Right x
collapseDefaults DefaultedValue   (SpecifiedValue y) = Right y
collapseDefaults DefaultedValue   DefaultedValue     = Right def

export
isDefaulted : WithDefault a def -> Bool
isDefaulted DefaultedValue = True
isDefaulted _              = False

export
isSpecified : WithDefault a def -> Bool
isSpecified DefaultedValue = False
isSpecified _              = True

public export
Eq a => Eq (WithDefault a def) where
  DefaultedValue   == DefaultedValue   = True
  DefaultedValue   == SpecifiedValue _ = False
  SpecifiedValue _ == DefaultedValue   = False
  SpecifiedValue x == SpecifiedValue y = x == y

public export
Ord a => Ord (WithDefault a def) where
  compare DefaultedValue   DefaultedValue       = EQ
  compare DefaultedValue   (SpecifiedValue _)   = LT
  compare (SpecifiedValue _) DefaultedValue     = GT
  compare (SpecifiedValue x) (SpecifiedValue y) = compare x y
