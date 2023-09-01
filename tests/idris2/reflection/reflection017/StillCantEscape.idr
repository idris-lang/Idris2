module StillCantEscape

import CanElabType

import Language.Reflection

%language ElabReflection

-- check that zero does not leak, should not typecheck
failing "CanElabType.T is private"

  T' : Type
  T' = %runElab elabExpr
