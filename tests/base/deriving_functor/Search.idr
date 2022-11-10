module Search

import Language.Reflection
import Language.Reflection.TTImp

%language ElabReflection

nothing : Maybe (Not Nat)
nothing = %runElab (search ?)

test : Search.nothing === Nothing
test = Refl
