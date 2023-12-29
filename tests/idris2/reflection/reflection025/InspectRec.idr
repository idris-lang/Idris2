module InspectRec

import Control.Monad.Writer

import Language.Reflection

%default total

%language ElabReflection

isFunc : NameInfo -> Bool
isFunc $ MkNameInfo Func = True
isFunc _                 = False

inspectRec : Elaboration m => (desc : String) -> a -> m a
inspectRec desc val = do
  expr <- quote val
  fns <- getCurrentFn
  let _ : Monoid Bool := Any
  rec <- execWriterT $ flip mapMTTImp expr $ \case
           e@(IVar fc nm) => do
             is <- getInfo nm
             let is = fst <$> filter (isFunc . snd) is
             refs <- map join $ for is $ \n => (n::) <$> getReferredFns n
             tell $ any (\fn => any (==fn) refs) fns
             pure e
           e => pure e
  logMsg "elab" 0 "case \{desc}: \{the String $ if rec then "recursive" else "non-recursive"}"
  pure val

----------------------------------------------

dec : Nat -> Nat
dec Z     = %runElab inspectRec "zero case" 0
dec (S n) = %runElab inspectRec "non-zero case" n

----------------------------------------------

simpleRec : Nat -> Nat
simpleRec Z     = %runElab inspectRec "base case" 10
simpleRec (S n) = %runElab inspectRec "next cast" $ simpleRec n

----------------------------------------------

mutualRec1 : Nat -> Nat
mutualRec2 : Nat -> Nat

mutualRec1 Z     = %runElab inspectRec "mutual rec 1, base" 11
mutualRec1 (S n) = %runElab inspectRec "mutual rec 1, next" $ mutualRec2 n

mutualRec2 Z     = %runElab inspectRec "mutual rec 2, base" 12
mutualRec2 (S n) = %runElab inspectRec "mutual rec 2, next" $ mutualRec1 n

----------------------------------------------

nestedMutRec1 : Nat -> Nat
nestedMutRec1 Z     = %runElab inspectRec "nestedMut rec 1, base" 11
nestedMutRec1 (S n) = %runElab inspectRec "nestedMut rec 1, next" $ nestedMutRec2 n where
  nestedMutRec2 : Nat -> Nat
  nestedMutRec2 Z     = %runElab inspectRec "nestedMut rec 2, base" 12
  nestedMutRec2 (S n) = %runElab inspectRec "nestedMut rec 2, next" $ nestedMutRec1 n
