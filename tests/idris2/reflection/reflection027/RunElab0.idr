module RunElab0

import Language.Reflection

%language ElabReflection

0 elabScript : Elab Unit
elabScript = pure ()

x : Unit
x = %runElab elabScript

%runElab elabScript
