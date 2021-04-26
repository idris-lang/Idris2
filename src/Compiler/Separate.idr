module Compiler.Separate

import public Core.Name
import public Libraries.Data.SortedMap

import Core.Hash
import Core.Name.Namespace

public export
ContentHash : Type
ContentHash = Int

export
record CompilationUnitId where
  constructor CUI
  contentHash : ContentHash

export
Eq CompilationUnitId where
  CUI x == CUI y = x == y

export
Ord CompilationUnitId where
  compare (CUI x) (CUI y) = compare x y

public export
record CompilationUnit def where
  constructor MkCompilationUnit
  id : CompilationUnitId
  contentHash : ContentHash
  dependencies : List CompilationUnitId
  definitions : List Name

export
mkCompilationUnits : List (Name, def) -> SortedMap CompilationUnitId (CompilationUnit def)
mkCompilationUnits defs = ?rhs
