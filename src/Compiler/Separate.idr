module Compiler.Separate

import public Core.Name
import public Core.Name.Namespace
import public Core.CompileExpr
import public Libraries.Data.SortedMap
import public Libraries.Data.SortedSet
import public Libraries.Data.StringMap

import Core.Hash
import Data.List
import Data.Vect

public export
ContentHash : Type
ContentHash = Int

export
record CompilationUnitId where
  constructor CUID
  id : Int

export
Eq CompilationUnitId where
  CUID x == CUID y = x == y

export
Ord CompilationUnitId where
  compare (CUID x) (CUID y) = compare x y

public export
record CompilationUnit def where
  constructor MkCompilationUnit
  id : CompilationUnitId
  contentHash : ContentHash
  namespaces : SortedSet Namespace
  dependencies : SortedSet CompilationUnitId
  definitions : List Name

private
getNS : Name -> Namespace
getNS (NS ns _) = ns
getNS _ = emptyNS

private
splitByNS : List (Name, def) -> List (Namespace, List (Name, def))
splitByNS = SortedMap.toList . foldl addOne SortedMap.empty
  where
    addOne
      : SortedMap Namespace (List (Name, def))
      -> (Name, def)
      -> SortedMap Namespace (List (Name, def))
    addOne nss ndef@(n, _) =
      SortedMap.mergeWith
        (++)
        (SortedMap.singleton (getNS n) [ndef])
        nss

-- https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm#The_algorithm_in_pseudocode
private
record TarjanVertex where
  constructor TV
  index : Int
  lowlink : Int
  inStack : Bool

private
record TarjanState cuid where
  constructor TS
  vertices : SortedMap cuid TarjanVertex
  stack : List cuid
  nextIndex : Int
  components : List (List cuid)
  impossibleHappened : Bool

private
tarjan : Ord cuid => SortedMap cuid (SortedSet cuid) -> List (List cuid)
tarjan {cuid} deps = loop initialState (SortedMap.keys deps)
  where
    initialState : TarjanState cuid
    initialState =
      TS
        SortedMap.empty
        []
        0
        []
        False

    strongConnect : TarjanState cuid -> cuid -> TarjanState cuid
    strongConnect ts v =
        let ts'' = case SortedMap.lookup v deps of
              Nothing => ts'  -- no edges
              Just edgeSet => loop ts' (SortedSet.toList edgeSet)
          in case SortedMap.lookup v ts''.vertices of
              Nothing => record { impossibleHappened = True } ts''
              Just vtv =>
                if vtv.index == vtv.lowlink
                  then createComponent ts'' v []
                  else ts''
      where
        createComponent : TarjanState cuid -> cuid -> List cuid -> TarjanState cuid
        createComponent ts v acc =
          case ts.stack of
            [] => record { impossibleHappened = True } ts
            w :: ws =>
              let ts' : TarjanState cuid = record {
                      vertices $= SortedMap.adjust w record{ inStack = False },
                      stack = ws
                    } ts
                in if w == v
                  then record { components $= ((v :: acc) ::) } ts'  -- that's it
                  else createComponent ts' v (w :: acc)

        loop : TarjanState cuid -> List cuid -> TarjanState cuid
        loop ts [] = ts
        loop ts (w :: ws) =
          loop (
            case SortedMap.lookup w ts.vertices of
              Nothing => let ts' = strongConnect ts w in
                case SortedMap.lookup w ts'.vertices of
                  Nothing => record { impossibleHappened = True } ts'
                  Just wtv => record { vertices $= SortedMap.adjust v record{ lowlink $= min wtv.lowlink } } ts'

              Just wtv => case wtv.inStack of
                False => ts  -- nothing to do
                True => record { vertices $= SortedMap.adjust v record{ lowlink $= min wtv.index } } ts
          ) ws

        ts' : TarjanState cuid
        ts' = record {
            vertices  $= SortedMap.insert v (TV ts.nextIndex ts.nextIndex True),
            stack     $= (v ::),
            nextIndex $= (1+)
          } ts

    loop : TarjanState cuid -> List cuid -> List (List cuid)
    loop ts [] =
      if ts.impossibleHappened
        then []
        else ts.components
    loop ts (v :: vs) =
      case SortedMap.lookup v ts.vertices of
        Just _ => loop ts vs  -- done, skip
        Nothing => loop (strongConnect ts v) vs

public export
interface HasNamespaces a where
  -- namespaces referred to from within
  nsRefs : a -> SortedSet Namespace

mutual
  export
  HasNamespaces NamedCExp where
    nsRefs (NmLocal fc n) = SortedSet.empty
    nsRefs (NmRef fc n) = SortedSet.singleton $ getNS n
    nsRefs (NmLam fc n rhs) = nsRefs rhs
    nsRefs (NmLet fc n val rhs) = nsRefs val <+> nsRefs rhs
    nsRefs (NmApp fc f args) = nsRefs f <+> concatMap nsRefs args
    nsRefs (NmCon fc cn tag args) = concatMap nsRefs args
    nsRefs (NmForce fc reason rhs) = nsRefs rhs
    nsRefs (NmDelay fc reason rhs) = nsRefs rhs
    nsRefs (NmErased fc) = SortedSet.empty
    nsRefs (NmPrimVal ft x) = SortedSet.empty
    nsRefs (NmOp fc op args) = concatMap nsRefs args
    nsRefs (NmExtPrim fc n args) = concatMap nsRefs args
    nsRefs (NmConCase fc scrut alts mbDflt) =
      nsRefs scrut <+> concatMap nsRefs alts <+> concatMap nsRefs mbDflt
    nsRefs (NmConstCase fc scrut alts mbDflt) =
      nsRefs scrut <+> concatMap nsRefs alts <+> concatMap nsRefs mbDflt
    nsRefs (NmCrash fc msg) = SortedSet.empty

  export
  HasNamespaces NamedConAlt where
    nsRefs (MkNConAlt n tag args rhs) = nsRefs rhs

  export
  HasNamespaces NamedConstAlt where
    nsRefs (MkNConstAlt c rhs) = nsRefs rhs

  export
  HasNamespaces NamedDef where
    nsRefs (MkNmFun argNs rhs) = nsRefs rhs
    nsRefs (MkNmCon tag arity nt) = SortedSet.empty
    nsRefs (MkNmForeign ccs fargs rty) = SortedSet.empty
    nsRefs (MkNmError rhs) = nsRefs rhs

-- compilation units sorted by number of imports, ascending
export
mkCompilationUnits : HasNamespaces def => List (Name, def) -> List (CompilationUnit def)
mkCompilationUnits {def} defs = unitsFrom 0 components
  where
    defsByNS : SortedMap Namespace (List (Name, def))
    defsByNS = SortedMap.fromList $ splitByNS defs

    defDepsRaw : List (SortedMap Namespace (SortedSet Namespace))
    defDepsRaw = [SortedMap.singleton (getNS n) (SortedSet.delete (getNS n) (nsRefs d)) | (n, d) <- defs]

    defDeps : SortedMap Namespace (SortedSet Namespace)
    defDeps = foldl (SortedMap.mergeWith SortedSet.union) SortedMap.empty defDepsRaw

    -- strongly connected components of the NS dep graph
    -- each SCC will become a compilation unit
    components : List (List Namespace)
    components = List.reverse $ tarjan defDeps  -- tarjan generates reverse toposort

    unitsFrom : Int -> List (List Namespace) -> List (CompilationUnit def)
    unitsFrom i [] = []
    unitsFrom i (nss :: nsss) =
      MkCompilationUnit
        (CUID i)
        ?hash
        (SortedSet.fromList nss)
        ?dependencies
        ?definitions
      :: unitsFrom (i+1) nsss
