
import Language.Reflection

%default total
%language ElabReflection

export infix 6 `op`

%runElab logSugaredTerm "debug" 0 "term with infix" `(a `op` b)

