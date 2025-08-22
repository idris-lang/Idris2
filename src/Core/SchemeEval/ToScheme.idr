module Core.SchemeEval.ToScheme

import Core.TT
import Libraries.Utils.Scheme

export
Scheme Namespace where
  toScheme x = toScheme (unsafeUnfoldNamespace x)
  fromScheme x = Just $ unsafeFoldNamespace !(fromScheme x)

export
Scheme UserName where
  toScheme (Basic str) = toScheme str
  toScheme (Field str) = Vector 5 [toScheme str]
  toScheme Underscore = Vector 9 []

  fromScheme (Vector 5 [x]) = pure $ Field !(fromScheme x)
  fromScheme (Vector 9 []) = pure Underscore
  fromScheme (StringVal x) = pure (Basic x)
  fromScheme _ = Nothing

export
Scheme Name where
  toScheme (NS x y) = Vector 0 [toScheme x, toScheme y]
  toScheme (UN x) = toScheme x
  toScheme (MN x y) = Vector 2 [toScheme x, toScheme y]
  toScheme (PV x y) = Vector 3 [toScheme x, toScheme y]
  toScheme (DN x y) = Vector 4 [toScheme x, toScheme y]
  toScheme (Nested x y) = Vector 6 [toScheme x, toScheme y]
  toScheme (CaseBlock x y) = Vector 7 [toScheme x, toScheme y]
  toScheme (WithBlock x y) = Vector 8 [toScheme x, toScheme y]
  toScheme (Resolved x) = toScheme x -- we'll see this most often

  fromScheme (Vector 0 [x, y])
      = pure $ NS !(fromScheme x) !(fromScheme y)
  fromScheme (Vector 2 [x, y])
      = pure $ MN !(fromScheme x) !(fromScheme y)
  fromScheme (Vector 3 [x, y])
      = pure $ PV !(fromScheme x) !(fromScheme y)
  fromScheme (Vector 4 [x, y])
      = pure $ DN !(fromScheme x) !(fromScheme y)
  fromScheme (Vector 5 [x, y])
      = pure $ UN (Field !(fromScheme x))
  fromScheme (Vector 6 [x, y])
      = pure $ Nested !(fromScheme x) !(fromScheme y)
  fromScheme (Vector 7 [x, y])
      = pure $ CaseBlock !(fromScheme x) !(fromScheme y)
  fromScheme (Vector 8 [x, y])
      = pure $ WithBlock !(fromScheme x) !(fromScheme y)
  fromScheme (Vector 9 [])
      = pure $ UN Underscore
  fromScheme (IntegerVal x)
      = pure $ Resolved (cast x)
  fromScheme (StringVal x)
      = pure $ UN (Basic x)
  fromScheme _ = Nothing

export
Scheme ModuleIdent where
  toScheme ns = toScheme (miAsNamespace ns)
  fromScheme s = Just $ nsAsModuleIdent !(fromScheme s)

export
Scheme OriginDesc where
  toScheme (PhysicalIdrSrc ident) = Vector 0 [toScheme ident]
  toScheme (PhysicalPkgSrc fname) = Vector 1 [toScheme fname]
  toScheme (Virtual ident) = Null

  fromScheme (Vector 0 [i]) = Just (PhysicalIdrSrc !(fromScheme i))
  fromScheme (Vector 1 [i]) = Just (PhysicalPkgSrc !(fromScheme i))
  fromScheme (Vector {}) = Nothing
  fromScheme _ = Just (Virtual Interactive)

export
Scheme FC where
  toScheme (MkFC d s e) = Vector 0 [toScheme d, toScheme s, toScheme e]
  toScheme (MkVirtualFC d s e) = Vector 1 [toScheme d, toScheme s, toScheme e]
  toScheme EmptyFC = Null

  fromScheme _ = Just EmptyFC

export
Scheme LazyReason where
  toScheme LInf = IntegerVal 0
  toScheme LLazy = IntegerVal 1
  toScheme LUnknown = IntegerVal 2

  fromScheme (IntegerVal 0) = Just LInf
  fromScheme (IntegerVal 1) = Just LLazy
  fromScheme _ = Just LUnknown

export
Scheme RigCount where
  toScheme x
      = if isErased x then IntegerVal 0
        else if isLinear x then IntegerVal 1
        else IntegerVal 2

  fromScheme (IntegerVal 0) = Just erased
  fromScheme (IntegerVal 1) = Just linear
  fromScheme _ = Just top

export
toSchemePi : PiInfo (SchemeObj Write) -> SchemeObj Write
toSchemePi Implicit = IntegerVal 0
toSchemePi Explicit = IntegerVal 1
toSchemePi AutoImplicit = IntegerVal 2
toSchemePi (DefImplicit s) = Box s

export
toSchemeWhy : WhyErased (SchemeObj Write) -> SchemeObj Write
toSchemeWhy Impossible = IntegerVal 0
toSchemeWhy Placeholder = IntegerVal 1
toSchemeWhy (Dotted s) = Box s
