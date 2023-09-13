module ElabScriptWarning

import Language.Reflection

%language ElabReflection

showsWarning : a -> b -> Elab c
showsWarning x y = do
  x' <- quote x
  warnAt (getFC x') "The first argument worth a warning"
  check =<< quote y






x : Nat
x = %runElab showsWarning "Suspicious" 15
