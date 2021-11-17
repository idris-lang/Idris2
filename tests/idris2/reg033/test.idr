import Language.Reflection
import DerivingEq

%language ElabReflection

-- This tree doesn't work

data TreeTwo a = BranchTwo (TreeTwo a) a (TreeTwo a)
               | Leaf

covering
Eq a => Eq (TreeTwo a) where
  (==) = %runElab genEq `{ TreeTwo }
