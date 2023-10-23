module DeclMacro

import public Language.Reflection

export %macro
macroFun : Nat -> Elab Nat
macroFun x = pure $ x + 1

export
justScript : Nat -> Elab Nat
justScript x = pure $ x + 2
