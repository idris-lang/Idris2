module TTImp.Elab.BindingApp

import Core.Core
import Core.FC
import Core.Name
import Core.WithName
import Core.Context
import Core.Normalise

import TTImp.TTImp

export
checkBindingApplication : WithFC Name -> WithFC (WithName RawImp) -> WithFC RawImp -> Core (Term vars, Glued vars)
checkBindingApplication nm bind scope = do
  -- check if the name in context is marked as binding
  -- - if it's typebind, check the bound variable is a Type
  -- - if it's autobind, infer the type from the scope
  --   - If the type is given explicitly, use that
  -- - if it's neither, report the error
  ?TODONext

