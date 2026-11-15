module Compiler.Opts.ToplevelConstants

import Core.CompileExpr
import Core.Context

import Data.List1
import Data.Vect
import Data.SortedSet
import Data.SortedMap
import Libraries.Data.Graph

--------------------------------------------------------------------------------
--          Call Graph
--------------------------------------------------------------------------------

-- direct calls from a top-level function's expression to other
-- top-level functions.
0 CallGraph : Type
CallGraph = SortedMap Name (SortedSet Name)

-- top-level functions called by an expression
calls : NamedCExp -> SortedSet Name
calls (NmLocal fc p) = empty
calls (NmRef fc n1) = singleton n1
calls (NmLam fc x y) = calls y
calls (NmLet fc x z w) = calls w <+> calls z
calls (NmApp fc x xs) = calls x <+> concatMap calls xs
calls (NmCon fc n1 x tag xs) = concatMap calls xs
calls (NmOp fc f xs) = concatMap calls xs
calls (NmExtPrim fc p xs) = concatMap calls xs
calls (NmForce fc lz x) = calls x
calls (NmDelay fc lz x) = calls x
calls (NmConCase fc sc xs x) =
  calls sc <+>
  concatMap (\(MkNConAlt _ _ _ _ y) => calls y) xs <+>
  concatMap calls x
calls (NmConstCase fc sc xs x) =
  calls sc <+>
  concatMap (\(MkNConstAlt _ y) => calls y) xs <+>
  concatMap calls x
calls (NmPrimVal fc cst) = empty
calls (NmErased fc) = empty
calls (NmCrash fc str) = empty

defCalls : NamedDef -> SortedSet Name
defCalls (MkNmFun args x) = calls x
defCalls (MkNmCon tag arity nt) = empty
defCalls (MkNmForeign ccs fargs x) = empty
defCalls (MkNmError x) = calls x

callGraph : List (Name, FC, NamedDef) -> CallGraph
callGraph = fromList . map (\(n,_,d) => (n, defCalls d))

isRecursive : CallGraph -> List1 Name -> Bool
isRecursive g (x ::: Nil) = maybe False (contains x) $ lookup x g
isRecursive _ _           = True

recursiveFunctions : CallGraph -> SortedSet Name
recursiveFunctions graph =
  let groups := filter (isRecursive graph) $ tarjan graph
   in concatMap (SortedSet.fromList . forget) groups

--------------------------------------------------------------------------------
--          Sorting Functions
--------------------------------------------------------------------------------

data SortTag : Type where

record SortST where
  constructor SST
  processed : SortedSet Name
  eager     : SortedSet Name
  triples   : SnocList (Name, FC, NamedDef)
  map       : SortedMap Name (Name, FC, NamedDef)
  graph     : CallGraph

appendDef : Ref SortTag SortST => (Name, FC, NamedDef) -> Core ()
appendDef t = do
  st <- get SortTag
  put SortTag $ {triples $= (:< t)} st

getCalls : Ref SortTag SortST => Name -> Core (List Name)
getCalls n = map (maybe [] Prelude.toList . lookup n . graph) (get SortTag)

getTriple : Ref SortTag SortST => Name -> Core (Maybe (Name,FC,NamedDef))
getTriple n = map (lookup n . map) (get SortTag)

markProcessed : Ref SortTag SortST => Name -> Core ()
markProcessed n = do
  st <- get SortTag
  put SortTag $ {processed $= insert n} st

isProcessed : Ref SortTag SortST => Name -> Core Bool
isProcessed n = map (contains n . processed) (get SortTag)

-- An expression that is already a value: evaluating it allocates at most
-- a constructor cell or a closure. It runs no user code, so it can neither
-- take long, nor crash, nor diverge, nor perform an effect.
-- `eager` holds the constants already emitted as plain values: a reference
-- to one of those is a variable reference.
isValue : (eager : SortedSet Name) -> NamedCExp -> Bool
isValue eager (NmPrimVal {})            = True
isValue eager (NmErased {})             = True
isValue eager (NmLam {})                = True
isValue eager (NmDelay {})              = True
isValue eager (NmRef {})                = True
isValue eager (NmCon _ _ _ _ xs)        = all (assert_total $ isValue eager) xs
isValue eager (NmApp _ (NmRef _ n) [])  = contains n eager
isValue eager _                         = False

-- A zero-argument definition is evaluated when the program is loaded only
-- if that costs nothing and cannot be observed: its body is a value and it
-- is not part of a recursive group (so that everything it mentions has been
-- defined before it). Every other zero-argument definition is evaluated at
-- its first use and remembered (see `schDef` in `Compiler.Scheme.Common`).
checkEager :  Ref SortTag SortST
           => (recursiveFunctions : SortedSet Name)
           -> (Name, FC, NamedDef)
           -> Core ()
checkEager rec (n, _, MkNmFun [] exp) = do
  st <- get SortTag
  when (not (contains n rec) && isValue st.eager exp) $
    put SortTag $ { eager $= insert n } st
checkEager _ _ = pure ()

sortDef :  Ref SortTag SortST
        => (recursiveFunctions : SortedSet Name)
        -> Name
        -> Core ()
sortDef rec n = do
  False  <- isProcessed n | True => pure ()
  markProcessed n
  cs     <- getCalls n
  traverse_ (sortDef rec) cs
  Just t <- getTriple n | Nothing => pure ()
  appendDef t
  checkEager rec t

||| Sorts the definitions so that each comes after the ones it calls, and
||| returns the names of the zero-argument definitions to be compiled to
||| plain values, evaluated when the program is loaded.
export
sortDefs : List (Name, FC, NamedDef) -> Core (List (Name, FC, NamedDef), SortedSet Name)
sortDefs ts =
  let graph  := callGraph ts
      rec    := recursiveFunctions graph
      init   := SST {
                    processed = empty
                  , eager     = empty
                  , triples   = Lin
                  , map       = fromList (map (\t => (fst t, t)) ts)
                  , graph     = graph
                  }
   in do
     s       <- newRef SortTag init
     traverse_ (sortDef rec) (map fst ts)
     st <- get SortTag
     pure (triples st <>> [], eager st)
