module TraverseWithConst

import Data.SortedSet
import Data.SortedMap           -- workaround for issue #2439
import Data.SortedMap.Dependent -- workaround for issue #2439

import Control.Applicative.Const

import Language.Reflection

names : TTImp -> SortedSet Name
names = runConst . mapATTImp' f where
  f : TTImp -> Const (SortedSet Name) TTImp -> Const (SortedSet Name) TTImp
  f (IVar _ n) = const $ MkConst $ SortedSet.singleton n
  f _          = id

%language ElabReflection

logNames : TTImp -> Elab ()
logNames expr = do
  logSugaredTerm "elab.test" 0 "term being analysed" expr
  logMsg "elab.test" 0 "- names: \{show $ Prelude.toList $ names expr}"

%runElab logNames `(f (a b) (c d))
%runElab logNames `(Prelude.id $ Prelude.pure 5)
%runElab logNames `(do
                      x <- action1 a b
                      y <- action2 b x
                      pure (x, y))
