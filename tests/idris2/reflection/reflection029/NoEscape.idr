module NoEscape

import Language.Reflection

%language ElabReflection

0 n : Nat
n = 3

0 elabScript : Elab Nat
elabScript = pure n

failing "n is not accessible in this context"

  m : Nat
  m = %runElab elabScript
