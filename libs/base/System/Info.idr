module System.Info

%extern prim__os : String
%extern prim__codegen : String

export
os : String
os = prim__os

export
codegen : String
codegen = prim__codegen

export
isWindows : Bool
isWindows = os `elem` ["windows", "mingw32", "cygwin32"]

%foreign "C:idris2_getNProcessors, libidris2_support"
prim__getNProcessors : PrimIO Int

export
getNProcessors : IO (Maybe Nat)
getNProcessors = do
  i <- fromPrim prim__getNProcessors
  pure (if i < 0 then Nothing else Just (integerToNat (cast i)))
