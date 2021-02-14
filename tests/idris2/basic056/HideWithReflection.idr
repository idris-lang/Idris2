import Data.List
import Data.List1
import Data.String

import Language.Reflection

%language ElabReflection

namespace A.B.C
  export
  name : ()

namespace A.B'.C
  export
  name : ()

disambig : String -> Name -> Elab Name
disambig str n = do
  let infixNS = reverse $ forget (split (== '.') str)
  names <- getType n
  let [one] = filter (f infixNS) (map fst names)
   | [] => fail "No name matches the query"
   | many => fail $ "Multiple names match the query: "
       ++ show many
  pure one
 where
  f : List String -> Name -> Bool
  f infixNS (NS (MkNS ns) name) = isInfixOf infixNS ns
  f _ _ = False

-- Picks A.B.C.name
Yay : Name
Yay = %runElab disambig "B" `{{name}}

Yay' : Name
Yay' = %runElab disambig "A.B" `{{name}}

sameName : Yay === Yay'
sameName = Refl

%runElab declare [ IHide EmptyFC Yay ]

-- Picks A.B'.C.name
-- No ambiguity, because A.B.C.name has been hidden
unit : ()
unit = name

